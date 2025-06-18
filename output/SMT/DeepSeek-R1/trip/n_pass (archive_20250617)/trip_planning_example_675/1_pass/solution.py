from z3 import *

def main():
    # Cities: Dubrovnik=0, Split=1, Milan=2, Porto=3, Krakow=4, Munich=5
    cities = ["Dubrovnik", "Split", "Milan", "Porto", "Krakow", "Munich"]
    n_cities = len(cities)
    
    # Allowed direct flights (bidirectional)
    connections = [
        (5, 3),  # Munich-Porto
        (1, 2),  # Split-Milan
        (2, 3),  # Milan-Porto
        (5, 4),  # Munich-Krakow
        (5, 2),  # Munich-Milan
        (0, 5),  # Dubrovnik-Munich
        (4, 1),  # Krakow-Split
        (4, 2),  # Krakow-Milan
        (5, 1)   # Munich-Split
    ]
    allowed_edges = set()
    for a, b in connections:
        allowed_edges.add((a, b))
        allowed_edges.add((b, a))
    
    # Durations: [Dubrovnik, Split, Milan, Porto, Krakow, Munich]
    durations = [4, 3, 3, 4, 2, 5]
    
    # Total days
    total_days = 16
    
    # Create solver
    s = Solver()
    
    # City variables: city0 to city16 (17 variables)
    city_vars = [Int(f"city{i}") for i in range(17)]
    for c in city_vars:
        s.add(c >= 0, c <= 5)
    
    # Travel variables: travel1 to travel16 (16 variables)
    travel_vars = [Bool(f"travel{i}") for i in range(1, 17)]
    
    # Constraints for travel: if travel_i, then (city_{i-1}, city_i) in allowed_edges; else, city_i == city_{i-1}
    for i in range(16):
        # For travel_vars[i] (which is travel_{i+1}), from city_vars[i] to city_vars[i+1]
        s.add(Implies(travel_vars[i], 
                      Or([And(city_vars[i] == a, city_vars[i+1] == b) for (a, b) in allowed_edges])))
        s.add(Implies(Not(travel_vars[i]), city_vars[i] == city_vars[i+1]))
    
    # Duration constraints for each city
    for c in range(6):
        # Count days starting in the city (city_vars[0] to city_vars[15] for days 1 to 16)
        count_start = Sum([If(city_vars[i] == c, 1, 0) for i in range(0, 16)])
        # Count travel arrivals: when travel_vars[i] is True and we arrive at city_vars[i+1] (city at end of day i+1)
        count_travel = Sum([If(And(travel_vars[i], city_vars[i+1] == c), 1, 0) for i in range(0, 16)])
        total_count = count_start + count_travel
        s.add(total_count == durations[c])
    
    # Event constraints
    # Munich: must be present on days 4,5,6,7,8
    for d in [4,5,6,7,8]:
        # Day d: start city is city_vars[d-1], travel on day d is travel_vars[d-1], end city is city_vars[d]
        s.add(Or(city_vars[d-1] == 5, And(travel_vars[d-1], city_vars[d] == 5)))
    # Milan: days 11,12,13
    for d in [11,12,13]:
        s.add(Or(city_vars[d-1] == 2, And(travel_vars[d-1], city_vars[d] == 2)))
    # Krakow: days 8,9
    for d in [8,9]:
        s.add(Or(city_vars[d-1] == 4, And(travel_vars[d-1], city_vars[d] == 4)))
    
    # Total travels must be 5
    s.add(Sum([If(t, 1, 0) for t in travel_vars]) == 5)
    
    # Check and output
    if s.check() == sat:
        m = s.model()
        # Get the values for city_vars and travel_vars
        city_vals = [m.evaluate(city_vars[i]).as_long() for i in range(17)]
        travel_vals = [m.evaluate(travel_vars[i]) for i in range(16)]
        
        # Output the plan
        for day in range(1, 17):
            start_city = city_vals[day-1]
            end_city = city_vals[day]
            travel = travel_vals[day-1]
            if travel:
                print(f"Day {day}: Travel from {cities[start_city]} to {cities[end_city]}")
            else:
                print(f"Day {day}: Stay in {cities[start_city]}")
        print("\nNote: The city at the start of day 1 is", cities[city_vals[0]])
        print("The city at the end of day 16 is", cities[city_vals[16]])
    else:
        print("No solution found")

if __name__ == "__main__":
    main()