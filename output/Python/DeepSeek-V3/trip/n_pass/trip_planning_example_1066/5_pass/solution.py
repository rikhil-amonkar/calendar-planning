import json
from itertools import permutations

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
    
    # Try all possible city orders (permutations)
    for city_order in permutations(city_days.keys()):
        days = [None] * 21  # Days 1-21 (index 0 = day 1)
        itinerary = []
        prev_city = None
        
        for city in city_order:
            days_needed = city_days[city]
            placed = False
            
            # Madrid must include day 20 or 21
            if city == 'Madrid':
                possible_starts = [19, 20]  # Starts that would cover day 20 or 21
            # Stuttgart must include at least one of days 1-4
            elif city == 'Stuttgart':
                possible_starts = range(1, 5 - days_needed + 2)
            else:
                possible_starts = range(1, 22 - days_needed + 1)
            
            # Try all possible start days for this city
            for start in possible_starts:
                end = start + days_needed - 1
                if end > 21:
                    continue
                
                # Check if all days in this range are available
                if all(days[i-1] is None for i in range(start, end + 1)):
                    # Check flight connection if not first city
                    if prev_city is None or city in connections[prev_city]:
                        # Place the city
                        for i in range(start, end + 1):
                            days[i-1] = city
                        itinerary.append({
                            'place': city,
                            'start_day': start,
                            'end_day': end
                        })
                        prev_city = city
                        placed = True
                        break
            
            if not placed:
                break  # This permutation doesn't work
        
        # Check if we successfully placed all cities
        if len(itinerary) == 8 and all(days):
            # Format the output
            formatted = []
            for entry in sorted(itinerary, key=lambda x: x['start_day']):
                formatted.append({
                    'day_range': f"Day {entry['start_day']}-{entry['end_day']}",
                    'place': entry['place']
                })
            return {'itinerary': formatted}
    
    return {'itinerary': []}

# Execute the function and print the result
print(json.dumps(find_itinerary()))