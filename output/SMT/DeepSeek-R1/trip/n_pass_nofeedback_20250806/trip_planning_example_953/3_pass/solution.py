from z3 import *
import json

def main():
    cities = ["Venice", "Salzburg", "Stockholm", "Frankfurt", "Florence", "Barcelona", "Stuttgart"]
    city_to_int = {c: i for i, c in enumerate(cities)}
    n_days = 18
    n_cities = 7

    # Create flight connection set
    allowed_edges = set()
    connections = [
        ("Barcelona", "Frankfurt"), ("Florence", "Frankfurt"),
        ("Stockholm", "Barcelona"), ("Barcelona", "Florence"),
        ("Venice", "Barcelona"), ("Stuttgart", "Barcelona"),
        ("Frankfurt", "Salzburg"), ("Stockholm", "Frankfurt"),
        ("Stuttgart", "Stockholm"), ("Stuttgart", "Frankfurt"),
        ("Venice", "Stuttgart"), ("Venice", "Frankfurt")
    ]
    for a, b in connections:
        i, j = city_to_int[a], city_to_int[b]
        allowed_edges.add((i, j))
        allowed_edges.add((j, i))

    # Initialize solver and variables
    s = Solver()
    start_city = [Int(f'start_{d}') for d in range(n_days)]
    flight = [Bool(f'flight_{d}') for d in range(n_days-1)]

    # Constraints
    s.add(start_city[0] == city_to_int["Venice"])  # Start in Venice
    
    for t in range(n_days-1):
        current, next_c = start_city[t], start_city[t+1]
        flight_taken = flight[t]
        valid_flight = Or(*[And(current == i, next_c == j) for (i, j) in allowed_edges])
        s.add(If(flight_taken, 
                And(current != next_c, valid_flight),
                current == next_c))

    # City day requirements
    reqs = {
        "Venice": 5, "Salzburg": 4, "Stockholm": 2,
        "Frankfurt": 4, "Florence": 4, "Barcelona": 2, "Stuttgart": 3
    }
    
    for city, days_needed in reqs.items():
        c = city_to_int[city]
        total = 0
        for t in range(n_days):
            if t < n_days-1:
                in_city = Or(start_city[t] == c, And(flight[t], start_city[t+1] == c))
            else:
                in_city = (start_city[t] == c)
            total += If(in_city, 1, 0)
        s.add(total == days_needed)
    
    # Venice days 1-5 constraint
    for t in range(5):
        if t < n_days-1:
            in_venice = Or(
                start_city[t] == city_to_int["Venice"],
                And(flight[t], start_city[t+1] == city_to_int["Venice"])
            )
        else:
            in_venice = (start_city[t] == city_to_int["Venice"])
        s.add(in_venice)

    # Solve and output itinerary
    if s.check() == sat:
        m = s.model()
        itinerary = []
        
        for day in range(n_days):
            start_val = m.eval(start_city[day]).as_long()
            cities_today = {cities[start_val]}
            if day < n_days-1:
                if m.eval(flight[day]):
                    next_val = m.eval(start_city[day+1]).as_long()
                    cities_today.add(cities[next_val])
            itinerary.append({
                "day": day + 1,
                "cities": sorted(list(cities_today))
            })
        
        print(json.dumps({"itinerary": itinerary}, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()