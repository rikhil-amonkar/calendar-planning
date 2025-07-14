from z3 import *
import json

def solve_itinerary():
    cities = {
        "Salzburg": 4,
        "Stockholm": 2,
        "Venice": 5,
        "Frankfurt": 4,
        "Florence": 4,
        "Barcelona": 2,
        "Stuttgart": 3
    }
    
    connections = {
        "Barcelona": ["Frankfurt", "Florence", "Stockholm", "Venice", "Stuttgart"],
        "Frankfurt": ["Barcelona", "Florence", "Salzburg", "Stockholm", "Stuttgart", "Venice"],
        "Florence": ["Barcelona", "Frankfurt"],
        "Stockholm": ["Barcelona", "Frankfurt", "Stuttgart"],
        "Venice": ["Barcelona", "Stuttgart", "Frankfurt"],
        "Stuttgart": ["Barcelona", "Stockholm", "Frankfurt", "Venice"],
        "Salzburg": ["Frankfurt"]
    }
    
    total_days = 18
    days = list(range(1, total_days + 1))
    
    s = Solver()
    
    city_names = list(cities.keys())
    city_to_idx = {city: idx for idx, city in enumerate(city_names)}
    num_cities = len(city_names)
    
    day_city = [Int(f"day_{d}_city") for d in days]
    
    for d in days:
        s.add(And(day_city[d-1] >= 0, day_city[d-1] < num_cities))
    
    for d in range(1, 6):
        s.add(day_city[d-1] == city_to_idx["Venice"])
    
    for city, req_days in cities.items():
        idx = city_to_idx[city]
        s.add(Sum([If(day_city[d-1] == idx, 1, 0) for d in days]) == req_days)
    
    for d in range(1, total_days):
        current_city = day_city[d-1]
        next_city = day_city[d]
        
        # Constraint: next city is either the same or a connected city
        same_city = current_city == next_city
        connected_cities = []
        for city, connected in connections.items():
            current_idx = city_to_idx[city]
            for connected_city in connected:
                connected_idx = city_to_idx[connected_city]
                connected_cities.append(And(current_city == current_idx, next_city == connected_idx))
        
        s.add(Or(same_city, Or(connected_cities)))
    
    if s.check() == sat:
        model = s.model()
        seq = []
        for d in days:
            city_idx = model.evaluate(day_city[d-1]).as_long()
            seq.append(city_names[city_idx])
        
        itinerary = []
        current_place = seq[0]
        start_day = 1
        
        for d in range(1, len(days) + 1):
            if d == len(days):
                itinerary.append({
                    "day_range": f"Day {start_day}-{d}",
                    "place": current_place
                })
                break
            
            if seq[d] != current_place:
                itinerary.append({
                    "day_range": f"Day {start_day}-{d}",
                    "place": current_place
                })
                itinerary.append({
                    "day_range": f"Day {d+1}",
                    "place": current_place
                })
                itinerary.append({
                    "day_range": f"Day {d+1}",
                    "place": seq[d]
                })
                start_day = d + 1
                current_place = seq[d]
        
        # Remove duplicate entries for the same day and place
        unique_itinerary = []
        seen = set()
        for entry in itinerary:
            key = (entry['day_range'], entry['place'])
            if key not in seen:
                seen.add(key)
                unique_itinerary.append(entry)
        
        return {"itinerary": unique_itinerary}
    else:
        return {"error": "No valid itinerary found"}

result = solve_itinerary()
print(json.dumps(result, indent=2))