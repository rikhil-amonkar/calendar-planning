from z3 import *
import json

def main():
    # City definitions and mappings
    cities = ["Venice", "Salzburg", "Stockholm", "Frankfurt", "Florence", "Barcelona", "Stuttgart"]
    city_to_int = {c: i for i, c in enumerate(cities)}
    n_days = 18
    n_cities = len(cities)
    
    # Flight connections (bidirectional)
    connections = [
        ("Barcelona", "Frankfurt"), ("Florence", "Frankfurt"),
        ("Stockholm", "Barcelona"), ("Barcelona", "Florence"),
        ("Venice", "Barcelona"), ("Stuttgart", "Barcelona"),
        ("Frankfurt", "Salzburg"), ("Stockholm", "Frankfurt"),
        ("Stuttgart", "Stockholm"), ("Stuttgart", "Frankfurt"),
        ("Venice", "Stuttgart"), ("Venice", "Frankfurt")
    ]
    allowed_pairs = []
    for a, b in connections:
        i, j = city_to_int[a], city_to_int[b]
        allowed_pairs.append((i, j))
        allowed_pairs.append((j, i))

    # Initialize solver
    s = Solver()
    
    # Day variables: start_city[d] = city at start of day d
    start_city = [Int(f'start_{d}') for d in range(n_days)]
    # Flight indicators: flight[d] = whether flight occurs on day d
    flight = [Bool(f'flight_{d}') for d in range(n_days-1)]

    # Constraints
    s.add(start_city[0] == city_to_int["Venice"])  # Start in Venice on day 1
    
    # Flight constraints
    for t in range(n_days-1):
        current = start_city[t]
        next_c = start_city[t+1]
        flight_taken = flight[t]
        
        # Flight condition: must use allowed route if flying
        flight_condition = Or([And(current == i, next_c == j) for i, j in allowed_pairs])
        s.add(If(flight_taken, flight_condition, current == next_c))
    
    # Total days per city requirements
    reqs = {
        "Venice": 5, "Salzburg": 4, "Stockholm": 2,
        "Frankfurt": 4, "Florence": 4, "Barcelona": 2, "Stuttgart": 3
    }
    
    for city, days_needed in reqs.items():
        c = city_to_int[city]
        total = 0
        for t in range(n_days):
            # On flight days, traveler is in both departure and arrival cities
            if t < n_days-1:
                present = Or(
                    start_city[t] == c,
                    And(flight[t], start_city[t+1] == c)
                )
            else:
                present = (start_city[t] == c)
            total += If(present, 1, 0)
        s.add(total == days_needed)
    
    # Must be in Venice on days 1-5
    for t in range(5):
        if t < n_days-1:
            in_venice = Or(
                start_city[t] == city_to_int["Venice"],
                And(flight[t], start_city[t+1] == city_to_int["Venice"])
            )
        else:
            in_venice = (start_city[t] == city_to_int["Venice"])
        s.add(in_venice)

    # Solve and generate itinerary
    if s.check() == sat:
        m = s.model()
        itinerary = []
        
        for day in range(n_days):
            # Get starting city for the day
            start_val = m.eval(start_city[day]).as_long()
            cities_today = {cities[start_val]}
            
            # If flight occurs, add arrival city
            if day < n_days-1:
                if m.eval(flight[day], model_completion=True) == True:
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