from z3 import *

def main():
    cities = ["Dubrovnik", "Split", "Milan", "Porto", "Krakow", "Munich"]
    n_cities = len(cities)
    
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
    
    durations = [4, 3, 3, 4, 2, 5]  # Dubrovnik, Split, Milan, Porto, Krakow, Munich
    total_days = 16
    
    s = Solver()
    
    city_vars = [Int(f"city{i}") for i in range(17)]
    for c in city_vars:
        s.add(c >= 0, c <= 5)
    
    travel_vars = [Bool(f"travel{i}") for i in range(1, 17)]
    
    for i in range(16):
        s.add(Implies(travel_vars[i], 
                      Or([And(city_vars[i] == a, city_vars[i+1] == b) for (a, b) in allowed_edges])))
        s.add(Implies(Not(travel_vars[i]), city_vars[i] == city_vars[i+1]))
    
    for c in range(6):
        count_start = Sum([If(city_vars[i] == c, 1, 0) for i in range(16)])
        count_travel = Sum([If(And(travel_vars[i], city_vars[i+1] == c), 1, 0) for i in range(16)])
        s.add(count_start + count_travel == durations[c])
    
    # Event constraints - no travel on event days
    # Munich: days 4,5,6,7,8
    for d in [4,5,6,7,8]:
        s.add(city_vars[d-1] == 5)
        s.add(Not(travel_vars[d-1]))
    # Krakow: days 8,9
    for d in [8,9]:
        s.add(city_vars[d-1] == 4)
        s.add(Not(travel_vars[d-1]))
    # Milan: days 11,12,13
    for d in [11,12,13]:
        s.add(city_vars[d-1] == 2)
        s.add(Not(travel_vars[d-1]))
    
    s.add(Sum([If(t, 1, 0) for t in travel_vars]) == 5)
    
    # Start and end constraints
    s.add(city_vars[0] == 0)  # Start in Dubrovnik
    s.add(city_vars[16] == 3)  # End in Porto
    
    if s.check() == sat:
        m = s.model()
        city_vals = [m.evaluate(city_vars[i]).as_long() for i in range(17)]
        travel_vals = [m.evaluate(travel_vars[i]) for i in range(16)]
        
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