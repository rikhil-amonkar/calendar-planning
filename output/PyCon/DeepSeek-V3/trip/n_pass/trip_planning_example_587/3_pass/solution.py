import json

def solve_itinerary():
    # Define the problem
    cities = {
        "Manchester": 3,
        "Istanbul": 7,
        "Venice": 7,
        "Krakow": 6,
        "Lyon": 2
    }
    
    total_days = 21
    
    # Direct flight connections
    connections = {
        "Manchester": ["Venice", "Istanbul", "Krakow"],
        "Venice": ["Manchester", "Istanbul", "Lyon"],
        "Istanbul": ["Manchester", "Venice", "Krakow", "Lyon"],
        "Krakow": ["Istanbul", "Manchester"],
        "Lyon": ["Venice", "Istanbul"]
    }
    
    def is_valid_itinerary(itinerary):
        # Check if all cities are visited exactly once
        visited_cities = set()
        for entry in itinerary:
            visited_cities.add(entry['place'])
        
        if len(visited_cities) != len(cities):
            return False
        
        # Check connection constraints
        for i in range(len(itinerary) - 1):
            current_city = itinerary[i]['place']
            next_city = itinerary[i + 1]['place']
            if next_city not in connections[current_city]:
                return False
        
        # Check Manchester constraint (must be within days 1-3)
        manchester_found = False
        for entry in itinerary:
            if entry['place'] == 'Manchester':
                start_day = int(entry['day_range'].split('-')[0].split(' ')[1])
                end_day = int(entry['day_range'].split('-')[-1]) if '-' in entry['day_range'] else start_day
                if start_day < 1 or end_day > 3:
                    return False
                manchester_found = True
                break
        
        if not manchester_found:
            return False
        
        # Check Venice constraint (must be within days 3-9)
        venice_found = False
        for entry in itinerary:
            if entry['place'] == 'Venice':
                start_day = int(entry['day_range'].split('-')[0].split(' ')[1])
                end_day = int(entry['day_range'].split('-')[-1]) if '-' in entry['day_range'] else start_day
                if start_day < 3 or end_day > 9:
                    return False
                venice_found = True
                break
        
        if not venice_found:
            return False
        
        # Check no overlapping days and total days <= 21
        days_used = set()
        for entry in itinerary:
            day_range = entry['day_range']
            if '-' in day_range:
                start = int(day_range.split('-')[0].split(' ')[1])
                end = int(day_range.split('-')[1])
                for day in range(start, end + 1):
                    if day in days_used:
                        return False
                    days_used.add(day)
            else:
                day = int(day_range.split(' ')[1])
                if day in days_used:
                    return False
                days_used.add(day)
        
        if max(days_used) > total_days:
            return False
        
        return True
    
    # Generate possible itineraries systematically
    def generate_itineraries(current_path, remaining_cities, all_paths):
        if not remaining_cities:
            all_paths.append(current_path[:])
            return
        
        for city in remaining_cities:
            if not current_path or city in connections[current_path[-1]]:
                new_remaining = [c for c in remaining_cities if c != city]
                generate_itineraries(current_path + [city], new_remaining, all_paths)
    
    all_paths = []
    generate_itineraries([], list(cities.keys()), all_paths)
    
    # Try to assign days to each path
    for path in all_paths:
        # Try different starting positions for Manchester and Venice
        for manchester_pos in range(len(path)):
            if path[manchester_pos] != 'Manchester':
                continue
            
            for venice_pos in range(len(path)):
                if path[venice_pos] != 'Venice':
                    continue
                
                # Try to assign days that satisfy constraints
                itinerary = []
                current_day = 1
                
                valid = True
                for i, city in enumerate(path):
                    # Calculate start day based on position and constraints
                    if city == 'Manchester':
                        # Manchester must be in days 1-3
                        if current_day > 1:
                            # Need to adjust to fit Manchester in days 1-3
                            if i > 0:
                                valid = False
                                break
                        start_day = 1
                    elif city == 'Venice':
                        # Venice must be in days 3-9
                        if current_day < 3:
                            start_day = 3
                        elif current_day > 9 - cities[city] + 1:
                            valid = False
                            break
                        else:
                            start_day = current_day
                    else:
                        start_day = current_day
                    
                    end_day = start_day + cities[city] - 1
                    
                    # Check if this exceeds total days
                    if end_day > total_days:
                        valid = False
                        break
                    
                    # Add to itinerary
                    if start_day == end_day:
                        day_range = f"Day {start_day}"
                    else:
                        day_range = f"Day {start_day}-{end_day}"
                    
                    itinerary.append({
                        "day_range": day_range,
                        "place": city
                    })
                    
                    # Update current day for next city
                    current_day = end_day + 1
                
                if valid and is_valid_itinerary(itinerary):
                    return {"itinerary": itinerary}
    
    return {"error": "No valid itinerary found"}

if __name__ == "__main__":
    result = solve_itinerary()
    print(json.dumps(result, indent=2))