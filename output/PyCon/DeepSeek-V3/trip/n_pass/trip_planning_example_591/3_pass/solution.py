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
    
    def find_itinerary(current_city, visited, days_used, itinerary):
        # Base case: all cities visited
        if len(visited) == len(cities):
            if days_used == total_days:
                return itinerary
            return None
        
        # Try visiting each unvisited city that has a direct flight
        for next_city in cities:
            if (next_city not in visited and 
                next_city in flight_connections[current_city]):
                
                days_needed = required_days[next_city]
                new_days_used = days_used + days_needed
                
                # Check if we exceed total days
                if new_days_used > total_days:
                    continue
                
                # Add to visited and itinerary
                new_visited = visited | {next_city}
                new_itinerary = itinerary + [next_city]
                
                # Recursively explore
                result = find_itinerary(next_city, new_visited, new_days_used, new_itinerary)
                if result:
                    return result
        
        return None
    
    # Start from Geneva
    start_city = 'Geneva'
    visited = {start_city}
    days_used = required_days[start_city]
    itinerary = [start_city]
    
    # Find valid itinerary
    result = find_itinerary(start_city, visited, days_used, itinerary)
    
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

if __name__ == "__main__":
    result = solve_trip_plan()
    print(json.dumps(result, indent=2))