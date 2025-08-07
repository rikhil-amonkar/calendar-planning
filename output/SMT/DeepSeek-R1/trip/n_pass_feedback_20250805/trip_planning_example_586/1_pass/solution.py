from z3 import *

def main():
    # City indices
    cities = ["Prague", "Lyon", "Frankfurt", "Helsinki", "Naples"]
    n_cities = len(cities)
    
    # Direct flights (undirected)
    flights = [
        (0, 1), (0, 2), (0, 3),
        (1, 2),
        (2, 3), (2, 4),
        (3, 4)
    ]
    
    # Create the solver
    s = Solver()
    
    # Variables: city[0] to city[12]
    city = [Int(f'city_{i}') for i in range(0, 13)]
    # fly[1] to fly[12]
    fly = [Bool(f'fly_{i}') for i in range(1, 13)]
    
    # Each city variable must be between 0 and 4
    for i in range(0, 13):
        s.add(city[i] >= 0, city[i] < n_cities)
    
    # Constraints for each day i from 1 to 12
    for i in range(1, 13):
        # If we don't fly, city remains the same
        no_fly_constraint = And(Not(fly[i-1]), city[i] == city[i-1])
        
        # If we fly, we must fly to a directly connected city
        fly_constraints = []
        for (a, b) in flights:
            fly_constraints.append(
                Or(
                    And(city[i-1] == a, city[i] == b),
                    And(city[i-1] == b, city[i] == a)
                )
            )
        fly_constraint = And(fly[i-1], Or(fly_constraints), city[i] != city[i-1])
        
        s.add(Or(no_fly_constraint, fly_constraint))
    
    # Exactly 4 flights
    flight_count = Sum([If(fly_i, 1, 0) for fly_i in fly])
    s.add(flight_count == 4)
    
    # Specific day constraints
    # Day 1: Must be in Prague
    s.add(Or(city[0] == 0, And(fly[0], city[1] == 0)))
    # Day 2: Must be in Prague
    s.add(Or(city[1] == 0, And(fly[1], city[2] == 0)))
    # Helsinki on days 2, 3, 4, 5
    for day, idx in [(2, 1), (3, 2), (4, 3), (5, 4)]:
        s.add(Or(city[idx] == 3, And(fly[idx], Or(city[idx] == 3, city[idx+1] == 3))))
    
    # Count the days per city
    counts = [0] * n_cities
    for c in range(n_cities):
        total = 0
        for i in range(1, 13):
            # If no flight on day i, then only the city at the start (city[i-1]) is visited
            # If flight, then both city[i-1] and city[i] are visited
            in_city = Or(
                And(Not(fly[i-1]), city[i-1] == c),
                And(fly[i-1], Or(city[i-1] == c, city[i] == c))
            )
            total += If(in_city, 1, 0)
        s.add(total == [2, 3, 3, 4, 4][c])
    
    # Check for a solution
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for day in range(1, 13):
            i = day - 1  # index for fly and city (fly index: 0-based for fly[0] to fly[11])
            if is_true(model[fly[i]]):
                start_city = model[city[i]].as_long()
                end_city = model[city[i+1]].as_long()
                city_list = [cities[start_city], cities[end_city]]
            else:
                c_val = model[city[i]].as_long()
                city_list = [cities[c_val]]
            itinerary.append({"day": day, "cities": city_list})
        
        result = {'itinerary': itinerary}
        print(result)
    else:
        print("No solution found")

if __name__ == '__main__':
    main()