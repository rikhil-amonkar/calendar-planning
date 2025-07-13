from z3 import *
import json

def solve_itinerary():
    # Cities and their required days
    cities = {
        "Porto": 5,
        "Prague": 4,
        "Reykjavik": 4,
        "Santorini": 2,
        "Amsterdam": 2,
        "Munich": 4
    }
    
    # Direct flights (bidirectional)
    direct_flights = [
        ("Porto", "Amsterdam"),
        ("Porto", "Munich"),
        ("Amsterdam", "Munich"),
        ("Amsterdam", "Reykjavik"),
        ("Amsterdam", "Santorini"),
        ("Amsterdam", "Prague"),
        ("Munich", "Reykjavik"),
        ("Munich", "Prague"),
        ("Reykjavik", "Prague")
    ]
    
    # Make sure the flight list is bidirectional
    flights = set()
    for a, b in direct_flights:
        flights.add((a, b))
        flights.add((b, a))
    
    total_days = 16
    city_names = sorted(cities.keys())
    city_index = {name: idx for idx, name in enumerate(city_names)}
    
    # Create a Z3 solver
    s = Solver()
    
    # Variables: for each day, the city we're in
    # day_city[d] is the city index for day d (0-based)
    day_city = [Int(f"day_{d}") for d in range(total_days)]
    for d in range(total_days):
        s.add(day_city[d] >= 0, day_city[d] < len(city_names))
    
    # Constraints: total days per city
    for city, days in cities.items():
        idx = city_index[city]
        s.add(Sum([If(day_city[d] == idx, 1, 0) for d in range(total_days)]) == days)
    
    # Constraints: events
    # Wedding in Reykjavik between day 4 and 7 (1-based)
    reykjavik_idx = city_index["Reykjavik"]
    s.add(Or([day_city[d] == reykjavik_idx for d in range(3, 7)]))  # days 4-7 (0-based 3-6)
    
    # Conference in Amsterdam on day 14 and 15 (1-based)
    amsterdam_idx = city_index["Amsterdam"]
    s.add(day_city[13] == amsterdam_idx)  # day 14 (0-based 13)
    s.add(day_city[14] == amsterdam_idx)  # day 15 (0-based 14)
    
    # Friend in Munich between day 7 and 10 (1-based)
    munich_idx = city_index["Munich"]
    s.add(Or([day_city[d] == munich_idx for d in range(6, 10)]))  # days 7-10 (0-based 6-9)
    
    # Constraints: flight connections
    for d in range(total_days - 1):
        current_city = day_city[d]
        next_city = day_city[d + 1]
        s.add(Or([And(current_city == city_index[a], next_city == city_index[b]) for a, b in flights]))
    
    # Check if the problem is satisfiable
    if s.check() == sat:
        m = s.model()
        itinerary = []
        
        # Determine the city for each day
        day_assignments = [m.evaluate(day_city[d]) for d in range(total_days)]
        day_assignments = [city_names[day_assignments[d].as_long()] for d in range(total_days)]
        
        # Build the itinerary
        current_city = day_assignments[0]
        start_day = 1
        for d in range(1, total_days):
            if day_assignments[d] == current_city:
                continue
            else:
                end_day = d
                itinerary.append({
                    "day_range": f"Day {start_day}-{end_day}",
                    "place": current_city
                })
                # Flight day: both cities on day d+1 (1-based)
                itinerary.append({
                    "day_range": f"Day {d + 1}",
                    "place": current_city
                })
                itinerary.append({
                    "day_range": f"Day {d + 1}",
                    "place": day_assignments[d]
                })
                current_city = day_assignments[d]
                start_day = d + 1
        # Add the last stay
        itinerary.append({
            "day_range": f"Day {start_day}-{total_days}",
            "place": current_city
        })
        
        # Remove duplicate entries for flight days
        unique_itinerary = []
        seen = set()
        for entry in itinerary:
            key = (entry["day_range"], entry["place"])
            if key not in seen:
                seen.add(key)
                unique_itinerary.append(entry)
        
        return {"itinerary": unique_itinerary}
    else:
        return {"itinerary": []}

# Execute the solver
result = solve_itinerary()
print(json.dumps(result, indent=2))