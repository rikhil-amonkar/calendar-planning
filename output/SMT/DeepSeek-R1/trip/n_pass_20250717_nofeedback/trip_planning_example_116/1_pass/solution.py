import json
from z3 import *

def main():
    n_days = 18
    n_cities = 3
    # Cities: 0: Split, 1: London, 2: Santorini
    city_names = ["Split", "London", "Santorini"]
    
    # Create the solver
    s = Solver()
    
    # present[d][c]: True if in city c on day d (0-indexed days: 0 to 17)
    present = [[Bool('present_d%dc%d' % (d, c)) for c in range(n_cities)] for d in range(n_days)]
    # flight[d]: True if flight on day d (0-indexed)
    flight = [Bool('flight_d%d' % d) for d in range(n_days)]
    
    # Day 1 and Day 18 are non-flight days
    s.add(flight[0] == False)   # Day 1
    s.add(flight[n_days-1] == False)  # Day 18
    
    # Fixed constraints: Day 12 and Day 18 in Santorini
    # Day 12 is index 11, Day 18 is index 17
    s.add(present[11][2] == True)  # Santorini on day 12
    s.add(present[17][2] == True)  # Santorini on day 18
    
    # Direct flight pairs: (Split, London) and (London, Santorini)
    for d in range(n_days):
        # For non-flight days: exactly one city
        s.add(Implies(Not(flight[d]), 
                      Or(
                         And(present[d][0], Not(present[d][1]), Not(present[d][2])),
                         And(Not(present[d][0]), present[d][1], Not(present[d][2])),
                         And(Not(present[d][0]), Not(present[d][1]), present[d][2])
                      )))
        # For flight days: exactly two cities that are connected
        s.add(Implies(flight[d],
                      Or(
                         And(present[d][0], present[d][1], Not(present[d][2])),  # Split and London
                         And(Not(present[d][0]), present[d][1], present[d][2])   # London and Santorini
                      )))
    
    # Total flight days = 2
    s.add(Sum([If(flight[d], 1, 0) for d in range(n_days)]) == 2)
    
    # Total days in each city
    s.add(Sum([If(present[d][0], 1, 0) for d in range(n_days)]) == 6)  # Split
    s.add(Sum([If(present[d][1], 1, 0) for d in range(n_days)]) == 7)  # London
    s.add(Sum([If(present[d][2], 1, 0) for d in range(n_days)]) == 7)  # Santorini
    
    # Consecutive days must share at least one city
    for d in range(n_days-1):
        s.add(Or(
            And(present[d][0], present[d+1][0]),
            And(present[d][1], present[d+1][1]),
            And(present[d][2], present[d+1][2])
        ))
    
    # Solve the problem
    if s.check() == sat:
        m = s.model()
        itinerary_list = []
        for d in range(n_days):
            day_number = d + 1
            for c in range(n_cities):
                if m.evaluate(present[d][c]):
                    itinerary_list.append({"day": day_number, "place": city_names[c]})
        result = {"itinerary": itinerary_list}
        print(json.dumps(result))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()