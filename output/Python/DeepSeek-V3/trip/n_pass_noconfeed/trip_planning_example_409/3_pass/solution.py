import json
from itertools import permutations

def find_itinerary():
    city_days = {
        'Hamburg': 2,
        'Zurich': 3,
        'Helsinki': 2,
        'Bucharest': 2,
        'Split': 7
    }
    
    connections = {
        'Zurich': ['Helsinki', 'Hamburg', 'Bucharest', 'Split'],
        'Helsinki': ['Zurich', 'Hamburg', 'Split'],
        'Hamburg': ['Zurich', 'Helsinki', 'Bucharest', 'Split'],
        'Bucharest': ['Zurich', 'Hamburg'],
        'Split': ['Zurich', 'Helsinki', 'Hamburg']
    }
    
    total_days = 12
    
    # Split must include days 4-10, so possible start days are:
    # - Day 1 (1-7) - covers days 4-7
    # - Day 2 (2-8) - covers days 4-8
    # - Day 3 (3-9) - covers days 4-9
    # - Day 4 (4-10) - covers days 4-10
    
    for split_start in range(1, 5):
        split_end = split_start + 6
        
        # Zurich must be 3 consecutive days (any days)
        for zurich_start in range(1, total_days - 2):
            zurich_end = zurich_start + 2
            
            # Check for overlap between Zurich and Split
            if not (zurich_end < split_start or zurich_start > split_end):
                continue  # can't be in two places at once
            
            # Now assign the remaining cities (Hamburg, Helsinki, Bucharest)
            remaining_cities = ['Hamburg', 'Helsinki', 'Bucharest']
            
            # Try all possible orders for remaining cities
            for city_order in permutations(remaining_cities):
                itinerary = []
                days_used = set()
                
                # Add Zurich to itinerary
                itinerary.append({
                    'day_range': f"Day {zurich_start}-{zurich_end}",
                    'place': 'Zurich'
                })
                days_used.update(range(zurich_start, zurich_end + 1))
                
                # Add Split to itinerary
                itinerary.append({
                    'day_range': f"Day {split_start}-{split_end}",
                    'place': 'Split'
                })
                days_used.update(range(split_start, split_end + 1))
                
                # Now schedule remaining cities
                current_day = 1
                valid = True
                
                for city in city_order:
                    required_days = city_days[city]
                    placed = False
                    
                    # Find earliest available consecutive days
                    for start in range(1, total_days - required_days + 2):
                        end = start + required_days - 1
                        if all(day not in days_used for day in range(start, end + 1)):
                            # Check flight connections
                            prev_city = itinerary[-1]['place'] if itinerary else None
                            if prev_city and city not in connections[prev_city]:
                                continue
                            
                            itinerary.append({
                                'day_range': f"Day {start}-{end}",
                                'place': city
                            })
                            days_used.update(range(start, end + 1))
                            placed = True
                            break
                    
                    if not placed:
                        valid = False
                        break
                
                if valid and len(days_used) == total_days:
                    # Check all cities are visited
                    visited_cities = {entry['place'] for entry in itinerary}
                    if visited_cities == set(city_days.keys()):
                        # Sort itinerary by day range
                        itinerary.sort(key=lambda x: int(x['day_range'].split('-')[0].split(' ')[1]))
                        return {"itinerary": itinerary}
    
    return {"itinerary": []}

result = find_itinerary()
print(json.dumps(result, indent=2))