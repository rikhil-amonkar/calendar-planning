import json

def find_itinerary():
    # Define the cities and their required days
    city_days = {
        'Brussels': 4,
        'Bucharest': 3,
        'Stuttgart': 4,
        'Mykonos': 2,
        'Madrid': 2,
        'Helsinki': 5,
        'Split': 3,
        'London': 5
    }
    
    # Define the direct flight connections
    connections = {
        'Helsinki': ['London', 'Madrid', 'Brussels', 'Split'],
        'Split': ['Madrid', 'Helsinki', 'London', 'Stuttgart'],
        'Madrid': ['Split', 'Helsinki', 'London', 'Mykonos', 'Bucharest', 'Brussels'],
        'London': ['Helsinki', 'Madrid', 'Brussels', 'Bucharest', 'Split', 'Mykonos', 'Stuttgart'],
        'Brussels': ['London', 'Bucharest', 'Helsinki', 'Madrid'],
        'Bucharest': ['London', 'Brussels', 'Madrid'],
        'Mykonos': ['Madrid', 'London'],
        'Stuttgart': ['London', 'Split']
    }
    
    # We'll use a backtracking approach to find a valid itinerary
    def backtrack(current_itinerary, remaining_cities, used_days):
        if len(used_days) == 21 and not remaining_cities:
            # Check constraints
            madrid_ok = False
            stuttgart_ok = False
            for entry in current_itinerary:
                start = entry['start_day']
                end = start + city_days[entry['place']] - 1
                days = set(range(start, end + 1))
                if entry['place'] == 'Madrid':
                    if 20 in days or 21 in days:
                        madrid_ok = True
                if entry['place'] == 'Stuttgart':
                    if any(d in days for d in range(1, 5)):
                        stuttgart_ok = True
            if madrid_ok and stuttgart_ok:
                return current_itinerary
            return None
            
        # Try adding each remaining city
        for city in remaining_cities:
            days_needed = city_days[city]
            
            # Find all possible positions to place this city
            for start_day in range(1, 22 - days_needed + 1):
                end_day = start_day + days_needed - 1
                new_days = set(range(start_day, end_day + 1))
                
                # Check if these days are available
                if new_days & used_days:
                    continue
                    
                # Check flight connection if this isn't the first city
                if current_itinerary:
                    last_city = current_itinerary[-1]['place']
                    if city not in connections[last_city]:
                        continue
                        
                # Check Madrid constraint
                if city == 'Madrid':
                    if not (20 in new_days or 21 in new_days):
                        continue
                        
                # Check Stuttgart constraint
                if city == 'Stuttgart':
                    if not any(d in new_days for d in range(1, 5)):
                        continue
                        
                # Add this city to itinerary
                new_itinerary = current_itinerary.copy()
                new_itinerary.append({
                    'place': city,
                    'start_day': start_day
                })
                new_remaining = remaining_cities.copy()
                new_remaining.remove(city)
                new_used = used_days.copy()
                new_used.update(new_days)
                
                result = backtrack(new_itinerary, new_remaining, new_used)
                if result:
                    return result
                    
        return None
        
    # Start with all cities remaining
    remaining_cities = list(city_days.keys())
    
    # Try starting with each city
    for start_city in remaining_cities:
        days_needed = city_days[start_city]
        
        # Find all possible starting days for this city
        for start_day in range(1, 22 - days_needed + 1):
            end_day = start_day + days_needed - 1
            days = set(range(start_day, end_day + 1))
            
            # Check constraints if this is Stuttgart or Madrid
            if start_city == 'Stuttgart' and not any(d in days for d in range(1, 5)):
                continue
            if start_city == 'Madrid' and not (20 in days or 21 in days):
                continue
                
            new_itinerary = [{
                'place': start_city,
                'start_day': start_day
            }]
            new_remaining = remaining_cities.copy()
            new_remaining.remove(start_city)
            new_used = days.copy()
            
            result = backtrack(new_itinerary, new_remaining, new_used)
            if result:
                # Format the itinerary
                formatted = []
                for entry in result:
                    start = entry['start_day']
                    end = start + city_days[entry['place']] - 1
                    formatted.append({
                        'day_range': f"Day {start}-{end}",
                        'place': entry['place']
                    })
                return {'itinerary': formatted}
    
    return {'itinerary': []}

# Execute the function and print the result
print(json.dumps(find_itinerary()))