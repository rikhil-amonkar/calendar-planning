import json

def solve_trip_plan():
    # Cities and their required days
    cities = ['Geneva', 'Munich', 'Valencia', 'Bucharest', 'Stuttgart']
    required_days = {
        'Geneva': 4,
        'Munich': 7,
        'Valencia': 6,
        'Bucharest': 2,
        'Stuttgart': 2
    }
    
    # Total days available
    total_days = 17
    
    # Flight connections (bidirectional)
    flight_connections = {
        'Geneva': ['Munich', 'Valencia'],
        'Munich': ['Geneva', 'Valencia', 'Bucharest'],
        'Valencia': ['Geneva', 'Munich', 'Bucharest', 'Stuttgart'],
        'Bucharest': ['Munich', 'Valencia'],
        'Stuttgart': ['Valencia']
    }
    
    def find_itinerary(start_city):
        # We'll use a more systematic approach - try different orders
        from itertools import permutations
        
        # Generate all possible orders of visiting the remaining cities
        remaining_cities = [city for city in cities if city != start_city]
        
        for city_order in permutations(remaining_cities):
            # Try this order
            current_path = [start_city]
            total_days_used = required_days[start_city]
            valid = True
            
            for i, next_city in enumerate(city_order):
                current_city = current_path[-1]
                
                # Check if there's a flight connection
                if next_city not in flight_connections[current_city]:
                    valid = False
                    break
                
                # Add days for the next city
                total_days_used += required_days[next_city]
                
                # Check if we exceed total days
                if total_days_used > total_days:
                    valid = False
                    break
                
                current_path.append(next_city)
            
            if valid and len(current_path) == len(cities):
                return current_path
        
        return None
    
    # Start from Geneva
    start_city = 'Geneva'
    
    # Find valid itinerary
    result = find_itinerary(start_city)
    
    if not result:
        # Try a different approach - allow partial itineraries if complete one isn't possible
        result = find_feasible_itinerary(start_city)
    
    if not result:
        return {"error": "No valid itinerary found"}
    
    # Calculate day ranges for the itinerary
    final_itinerary = []
    current_day = 1
    
    for i, city in enumerate(result):
        days_in_city = required_days[city]
        end_day = current_day + days_in_city - 1
        
        if current_day == end_day:
            day_range = f"Day {current_day}"
        else:
            day_range = f"Day {current_day}-{end_day}"
        
        final_itinerary.append({
            "day_range": day_range,
            "place": city
        })
        
        current_day = end_day + 1
    
    return {"itinerary": final_itinerary}

def find_feasible_itinerary(start_city):
    cities = ['Geneva', 'Munich', 'Valencia', 'Bucharest', 'Stuttgart']
    required_days = {
        'Geneva': 4,
        'Munich': 7,
        'Valencia': 6,
        'Bucharest': 2,
        'Stuttgart': 2
    }
    total_days = 17
    flight_connections = {
        'Geneva': ['Munich', 'Valencia'],
        'Munich': ['Geneva', 'Valencia', 'Bucharest'],
        'Valencia': ['Geneva', 'Munich', 'Bucharest', 'Stuttgart'],
        'Bucharest': ['Munich', 'Valencia'],
        'Stuttgart': ['Valencia']
    }
    
    # Use BFS to find a path that visits all cities
    from collections import deque
    
    # Start state: (current_city, visited_set, days_used, path)
    queue = deque()
    initial_visited = frozenset([start_city])
    queue.append((start_city, initial_visited, required_days[start_city], [start_city]))
    
    best_path = None
    
    while queue:
        current_city, visited, days_used, path = queue.popleft()
        
        # If we've visited all cities and are within day limit, we found a solution
        if len(visited) == len(cities) and days_used <= total_days:
            if best_path is None or days_used < sum(required_days[city] for city in best_path):
                best_path = path
        
        # Try all possible next cities
        for next_city in cities:
            if (next_city not in visited and 
                next_city in flight_connections[current_city]):
                
                new_days = days_used + required_days[next_city]
                
                # Only proceed if we don't exceed total days
                if new_days <= total_days:
                    new_visited = visited | frozenset([next_city])
                    new_path = path + [next_city]
                    queue.append((next_city, new_visited, new_days, new_path))
    
    return best_path

if __name__ == "__main__":
    result = solve_trip_plan()
    print(json.dumps(result, indent=2))