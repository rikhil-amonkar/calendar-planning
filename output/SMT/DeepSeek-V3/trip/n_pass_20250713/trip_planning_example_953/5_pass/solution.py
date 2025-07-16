from z3 import *
import json

def solve_itinerary():
    # Cities and required days
    cities = {
        "Salzburg": 4,
        "Stockholm": 2,
        "Venice": 5,
        "Frankfurt": 4,
        "Florence": 4,
        "Barcelona": 2,
        "Stuttgart": 3
    }
    
    # Direct flights (undirected)
    direct_flights = [
        ("Barcelona", "Frankfurt"),
        ("Florence", "Frankfurt"),
        ("Stockholm", "Barcelona"),
        ("Barcelona", "Florence"),
        ("Venice", "Barcelona"),
        ("Stuttgart", "Barcelona"),
        ("Frankfurt", "Salzburg"),
        ("Stockholm", "Frankfurt"),
        ("Stuttgart", "Stockholm"),
        ("Stuttgart", "Frankfurt"),
        ("Venice", "Stuttgart"),
        ("Venice", "Frankfurt")
    ]
    
    # Create flight connections
    flight_connections = {}
    for city in cities:
        flight_connections[city] = []
    for a, b in direct_flights:
        flight_connections[a].append(b)
        flight_connections[b].append(a)
    
    total_days = 18
    Day = 18  # Days are 1-based to 18
    
    # Create Z3 variables: city per day
    day_city = [Int(f"day_{d}_city") for d in range(1, Day + 1)]
    
    # City to integer mapping
    city_to_int = {city: idx for idx, city in enumerate(cities.keys())}
    int_to_city = {idx: city for idx, city in enumerate(cities.keys())}
    
    s = Solver()
    
    # Each day_city must be a valid city index
    for d in range(Day):
        s.add(day_city[d] >= 0, day_city[d] < len(cities))
    
    # Constraint: Venice must be visited from day 1 to day 5 (inclusive)
    for d in range(5):
        s.add(day_city[d] == city_to_int["Venice"])
    
    # Constraints on number of days per city
    for city, days in cities.items():
        city_idx = city_to_int[city]
        s.add(Sum([If(day_city[d] == city_idx, 1, 0) for d in range(Day)]) == days)
    
    # Flight constraints: consecutive days must be same city or connected
    for d in range(Day - 1):
        current = day_city[d]
        next_ = day_city[d + 1]
        same_city = current == next_
        connected = Or([And(current == city_to_int[a], next_ == city_to_int[b]) 
                       for a, b in direct_flights] + 
                      [And(current == city_to_int[b], next_ == city_to_int[a]) 
                       for a, b in direct_flights])
        s.add(Or(same_city, connected))
    
    # Check if model is satisfiable
    if s.check() == sat:
        m = s.model()
        sequence = []
        for d in range(Day):
            city_idx = m.evaluate(day_city[d]).as_long()
            city = int_to_city[city_idx]
            sequence.append(city)
        
        # Build itinerary with flight days
        itinerary = []
        current = sequence[0]
        start = 1
        
        for d in range(1, Day):
            if sequence[d] != sequence[d-1]:
                # Add stay before flight
                if start <= d:
                    itinerary.append({
                        "day_range": f"Day {start}-{d}",
                        "place": sequence[d-1]
                    })
                # Add flight day (both cities)
                itinerary.append({
                    "day_range": f"Day {d}",
                    "place": sequence[d-1]
                })
                itinerary.append({
                    "day_range": f"Day {d}",
                    "place": sequence[d]
                })
                start = d + 1
        
        # Add last stay
        itinerary.append({
            "day_range": f"Day {start}-{Day}",
            "place": sequence[-1]
        })
        
        # Verify day counts
        day_counts = {city: 0 for city in cities}
        for entry in itinerary:
            if '-' in entry["day_range"]:
                start, end = map(int, entry["day_range"][4:].split('-'))
                days = end - start + 1
            else:
                days = 1
            day_counts[entry["place"]] += days
        
        for city, days in cities.items():
            assert day_counts[city] == days, f"Day count mismatch for {city}"
        
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

# Execute and print result
result = solve_itinerary()
print(json.dumps(result, indent=2))