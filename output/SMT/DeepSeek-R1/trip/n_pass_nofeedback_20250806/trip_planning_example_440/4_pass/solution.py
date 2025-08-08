import json

def main():
    cities = ["Split", "Helsinki", "Reykjavik", "Vilnius", "Geneva"]
    durations = [2, 2, 3, 3, 6]
    city_indices = {city: idx for idx, city in enumerate(cities)}
    
    # Direct flight connections (bidirectional)
    connections = [
        ("Split", "Helsinki"),
        ("Geneva", "Split"),
        ("Geneva", "Helsinki"),
        ("Helsinki", "Reykjavik"),
        ("Vilnius", "Helsinki"),
        ("Split", "Vilnius")
    ]
    allowed_pairs = set()
    for a, b in connections:
        allowed_pairs.add((a, b))
        allowed_pairs.add((b, a))
    
    # Constraints
    def is_valid_connection(current, next_city):
        return (current, next_city) in allowed_pairs
    
    def satisfies_events(itinerary):
        reykjavik_days = [day for day, city in itinerary if city == "Reykjavik"]
        vilnius_days = [day for day, city in itinerary if city == "Vilnius"]
        return (any(10 <= day <= 12 for day in reykjavik_days) and 
                any(7 <= day <= 9 for day in vilnius_days))
    
    # Backtracking to find valid itinerary
    def backtrack(path, used, day, last_city):
        if day > 12:
            return None
            
        if len(path) == 5 and day == 13 and satisfies_events(path):
            return path
            
        for idx, city in enumerate(cities):
            if used[idx]:
                continue
                
            if last_city and not is_valid_connection(last_city, city):
                continue
                
            used[idx] = True
            dur = durations[idx]
            new_path = path + [(d, city) for d in range(day, day + dur)]
            
            # Recurse to next city
            result = backtrack(new_path, used, day + dur - 1, city)
            if result:
                return result
                
            used[idx] = False
            
        return None
    
    # Start search from each city as first city
    solution = None
    for start_idx in range(5):
        used = [False] * 5
        used[start_idx] = True
        start_city = cities[start_idx]
        dur = durations[start_idx]
        path = [(d, start_city) for d in range(1, 1 + dur)]
        solution = backtrack(path, used, 1 + dur - 1, start_city)
        if solution:
            break
            
    if solution:
        # Format the itinerary
        itinerary = [{"day": day, "place": city} for day, city in solution]
        print(json.dumps({"itinerary": itinerary}, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()