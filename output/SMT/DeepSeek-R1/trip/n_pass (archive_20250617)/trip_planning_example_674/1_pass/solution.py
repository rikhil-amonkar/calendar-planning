from z3 import *

def main():
    # Cities and their indices
    cities = ["Helsinki", "Warsaw", "Madrid", "Split", "Reykjavik", "Budapest"]
    c2i = {city: idx for idx, city in enumerate(cities)}
    i2c = {idx: city for idx, city in enumerate(cities)}
    n_cities = len(cities)
    n_days = 14
    n_flight_days = 13  # Days 1 to 13 (can fly)

    # Directed flights: (from, to)
    directed_flights = [
        (c2i["Helsinki"], c2i["Reykjavik"]),
        (c2i["Reykjavik"], c2i["Helsinki"]),
        (c2i["Budapest"], c2i["Warsaw"]),
        (c2i["Warsaw"], c2i["Budapest"]),
        (c2i["Madrid"], c2i["Split"]),
        (c2i["Split"], c2i["Madrid"]),
        (c2i["Helsinki"], c2i["Split"]),
        (c2i["Split"], c2i["Helsinki"]),
        (c2i["Helsinki"], c2i["Madrid"]),
        (c2i["Madrid"], c2i["Helsinki"]),
        (c2i["Helsinki"], c2i["Budapest"]),
        (c2i["Budapest"], c2i["Helsinki"]),
        (c2i["Reykjavik"], c2i["Warsaw"]),
        (c2i["Warsaw"], c2i["Reykjavik"]),
        (c2i["Helsinki"], c2i["Warsaw"]),
        (c2i["Warsaw"], c2i["Helsinki"]),
        (c2i["Madrid"], c2i["Budapest"]),
        (c2i["Budapest"], c2i["Madrid"]),
        (c2i["Budapest"], c2i["Reykjavik"]),
        (c2i["Reykjavik"], c2i["Budapest"]),
        (c2i["Madrid"], c2i["Warsaw"]),
        (c2i["Warsaw"], c2i["Madrid"]),
        (c2i["Warsaw"], c2i["Split"]),
        (c2i["Split"], c2i["Warsaw"]),
        (c2i["Reykjavik"], c2i["Madrid"])
    ]

    # Required days per city
    required_days = [2, 3, 4, 4, 2, 4]  # Helsinki, Warsaw, Madrid, Split, Reykjavik, Budapest

    # Create solver
    s = Solver()

    # Variables: L[0] to L[13] for day1 to day14
    L = [Int(f'L_{i}') for i in range(n_days)]
    fly = [Bool(f'fly_{i}') for i in range(n_flight_days)]  # fly[0] for flight on day1, fly[12] for flight on day13

    # Constraint: L[i] must be between 0 and n_cities-1
    for i in range(n_days):
        s.add(L[i] >= 0, L[i] < n_cities)

    # Start in Helsinki (index0) on day1
    s.add(L[0] == c2i["Helsinki"])

    # Constraints for flights
    for i in range(n_flight_days):
        # If fly[i] is True, then (L[i], L[i+1]) must be in directed_flights
        # Otherwise, L[i] == L[i+1]
        options = []
        for (f, t) in directed_flights:
            options.append(And(L[i] == f, L[i+1] == t))
        s.add(If(fly[i], Or(options), L[i] == L[i+1]))

    # Total flights must be 5
    s.add(Sum([If(fly[i], 1, 0) for i in range(n_flight_days)]) == 5)

    # Constraints for required days per city and fixed days
    for c in range(n_cities):
        total = 0
        for d in range(n_days):
            if d < n_flight_days:
                in_c = Or(L[d] == c, And(fly[d], L[d+1] == c))
            else:
                in_c = (L[d] == c)
            total += If(in_c, 1, 0)
        s.add(total == required_days[c])

    # Fixed constraints for specific days
    # Helsinki must be on day1 (d0) and day2 (d1)
    # For d0: in_helsinki = L[0]==0 or (fly[0] and L[1]==0) -> but L[0]=0, so true.
    # For d1: in_helsinki = Or(L[1]==0, And(fly[1], L[2]==0))
    s.add(Or(L[1] == c2i["Helsinki"], And(fly[1], L[2] == c2i["Helsinki"])))
    
    # Reykjavik must be on day8 (d7) and day9 (d8)
    s.add(Or(L[7] == c2i["Reykjavik"], And(fly[7], L[8] == c2i["Reykjavik"])))
    s.add(Or(L[8] == c2i["Reykjavik"], And(fly[8], L[9] == c2i["Reykjavik"])))
    
    # Warsaw must be on day9 (d8), day10 (d9), day11 (d10)
    s.add(Or(L[8] == c2i["Warsaw"], And(fly[8], L[9] == c2i["Warsaw"])))
    s.add(Or(L[9] == c2i["Warsaw"], And(fly[9], L[10] == c2i["Warsaw"])))
    s.add(Or(L[10] == c2i["Warsaw"], And(fly[10], L[11] == c2i["Warsaw"])))

    # Additional constraints to fix known values and reduce search space
    s.add(fly[0] == False)  # No flight on day1 (since we start in Helsinki and must be there on day2)
    s.add(fly[1] == True)   # Flight on day2 (leave Helsinki)
    s.add(fly[8] == True)   # Flight on day9 (from Reykjavik to Warsaw)
    s.add(L[8] == c2i["Reykjavik"])
    s.add(L[9] == c2i["Warsaw"])
    
    # Flight from Helsinki on day2 must be to a directly connected city
    possible_next = []
    for (f, t) in directed_flights:
        if f == c2i["Helsinki"]:
            possible_next.append(L[2] == t)
    s.add(Or(possible_next))

    # Constraints to not be in Helsinki after day2, Reykjavik outside days 8-9, Warsaw outside days 9-11
    for d in range(n_days):
        if d not in [0, 1]:
            # Not in Helsinki
            if d < n_flight_days:
                in_hel = Or(L[d] == c2i["Helsinki"], And(fly[d], L[d+1] == c2i["Helsinki"]))
            else:
                in_hel = (L[d] == c2i["Helsinki"])
            s.add(Not(in_hel))
        
        if d not in [7, 8]:
            # Not in Reykjavik
            if d < n_flight_days:
                in_rey = Or(L[d] == c2i["Reykjavik"], And(fly[d], L[d+1] == c2i["Reykjavik"]))
            else:
                in_rey = (L[d] == c2i["Reykjavik"])
            s.add(Not(in_rey))
        
        if d not in [8, 9, 10]:
            # Not in Warsaw
            if d < n_flight_days:
                in_war = Or(L[d] == c2i["Warsaw"], And(fly[d], L[d+1] == c2i["Warsaw"]))
            else:
                in_war = (L[d] == c2i["Warsaw"])
            s.add(Not(in_war))

    # Solve the problem
    if s.check() == sat:
        m = s.model()
        # Print the plan
        print("Day\tStart City\tFlight To\tCities Visited (during the day)")
        for d in range(n_days):
            start_city = i2c[m.evaluate(L[d]).as_long()]
            if d < n_flight_days:
                fly_today = m.evaluate(fly[d])
                if fly_today:
                    next_city = i2c[m.evaluate(L[d+1]).as_long()]
                    flight_str = f"{start_city} to {next_city}"
                    visited = f"{start_city}, {next_city}"
                else:
                    flight_str = "None"
                    visited = start_city
            else:
                flight_str = "None"
                visited = start_city
            print(f"{d+1}\t{start_city}\t\t{flight_str}\t\t{visited}")
    else:
        print("No solution found")

if __name__ == '__main__':
    main()