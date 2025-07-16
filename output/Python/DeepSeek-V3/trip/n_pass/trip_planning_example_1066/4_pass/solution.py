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
    
    # Corrected city names (fixing typos)
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
    
    # Try all possible city orders (permutations)
    for city_order in permutations(city_days.keys()):
        # Initialize day assignments
        days = [None] * 21  # Days 1-21 (index 0 = day 1)
        itinerary = []
        
        try:
            current_day = 1
            prev_city = None
            
            for city in city_order:
                days_needed = city_days[city]
                
                # Find earliest available slot that meets constraints
                found = False
                
                # For Madrid, must include day 20 or 21
                if city == 'Madrid':
                    # Try placing at day 19 (ends day 20) or day 20 (ends day 21)
                    for start in [19, 20]:
                        if start + days_needed - 1 <= 21:
                            if all(days[i-1] is None for i in range(start, start + days_needed)):
                                # Check flight connection
                                if prev_city is None or city in connections[prev_city]:
                                    # Assign days
                                    for i in range(start, start + days_needed):
                                        days[i-1] = city
                                    itinerary.append({
                                        'place': city,
                                        'start_day': start,
                                        'end_day': start + days_needed - 1
                                    })
                                    prev_city = city
                                    found = True
                                    break
                    if found:
                        continue
                
                # For Stuttgart, must include at least one of days 1-4
                elif city == 'Stuttgart':
                    # Try placing to cover at least one of days 1-4
                    for start in range(1, 5 - days_needed + 2):
                        if start + days_needed - 1 <= 21:
                            if all(days[i-1] is None for i in range(start, start + days_needed)):
                                # Check flight connection
                                if prev_city is None or city in connections[prev_city]:
                                    # Assign days
                                    for i in range(start, start + days_needed):
                                        days[i-1] = city
                                    itinerary.append({
                                        'place': city,
                                        'start_day': start,
                                        'end_day': start + days_needed - 1
                                    })
                                    prev_city = city
                                    found = True
                                    break
                    if found:
                        continue
                
                # For other cities, find earliest available slot
                for start in range(1, 22 - days_needed + 1):
                    if all(days[i-1] is None for i in range(start, start + days_needed)):
                        # Check flight connection
                        if prev_city is None or city in connections[prev_city]:
                            # Assign days
                            for i in range(start, start + days_needed):
                                days[i-1] = city
                            itinerary.append({
                                'place': city,
                                'start_day': start,
                                'end_day': start + days_needed - 1
                            })
                            prev_city = city
                            found = True
                            break
                if not found:
                    break  # This permutation doesn't work
            
            # If we successfully placed all cities
            if len(itinerary) == 8 and all(days):
                # Format the output
                formatted = []
                for entry in sorted(itinerary, key=lambda x: x['start_day']):
                    formatted.append({
                        'day_range': f"Day {entry['start_day']}-{entry['end_day']}",
                        'place': entry['place']
                    })
                return {'itinerary': formatted}
                
        except:
            continue
    
    return {'itinerary': []}

# Execute the function and print the result
print(json.dumps(find_itinerary()))