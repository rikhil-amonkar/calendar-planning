import json

def find_itinerary():
    # Cities and required days
    cities = {
        "Helsinki": 4,
        "Valencia": 5,
        "Dubrovnik": 4,
        "Porto": 3,
        "Prague": 3,
        "Reykjavik": 4
    }
    
    # Direct flights (from -> to)
    flights = {
        "Helsinki": ["Prague", "Reykjavik", "Dubrovnik"],
        "Prague": ["Helsinki", "Valencia", "Reykjavik"],
        "Valencia": ["Prague", "Porto"],
        "Porto": ["Valencia"],
        "Reykjavik": ["Helsinki", "Prague"],
        "Dubrovnik": ["Helsinki"]
    }
    
    # Porto must be between day 16-18 (inclusive)
    porto_constraint = (16, 18)
    
    def backtrack(current_city, visited, current_day, itinerary):
        # Base case: all cities visited and exactly 18 days used
        if len(visited) == len(cities) and current_day == 19:
            return itinerary.copy()
        
        for city in cities:
            if city not in visited:
                # Check flight connection
                if current_city and city not in flights.get(current_city, []):
                    continue
                
                days_needed = cities[city]
                end_day = current_day + days_needed - 1
                
                # Check total days don't exceed 18
                if end_day > 18:
                    continue
                
                # Special check for Porto
                if city == "Porto":
                    if not (porto_constraint[0] <= current_day and end_day <= porto_constraint[1]):
                        continue
                
                # Add to itinerary
                new_entry = {
                    "day_range": f"Day {current_day}-{end_day}",
                    "place": city
                }
                itinerary.append(new_entry)
                visited.add(city)
                
                # Recursive call
                result = backtrack(city, visited, end_day + 1, itinerary)
                if result:
                    return result
                
                # Backtrack
                itinerary.pop()
                visited.remove(city)
        
        return None
    
    # Try starting from each city
    for start_city in cities:
        initial_days = cities[start_city]
        if initial_days > 18:
            continue  # Skip if starting city alone exceeds the limit
            
        result = backtrack(start_city, {start_city}, initial_days + 1, [{
            "day_range": f"Day 1-{initial_days}",
            "place": start_city
        }])
        if result:
            return {"itinerary": result}
    
    return {"itinerary": []}

# Execute and print the result
result = find_itinerary()
print(json.dumps(result, indent=2))