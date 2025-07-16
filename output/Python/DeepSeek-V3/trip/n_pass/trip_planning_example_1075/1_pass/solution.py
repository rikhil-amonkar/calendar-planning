import json
from itertools import permutations

def find_itinerary():
    # Cities and required days
    cities = {
        'Vienna': 4,
        'Lyon': 3,
        'Edinburgh': 4,
        'Reykjavik': 5,
        'Stuttgart': 5,
        'Manchester': 2,
        'Split': 5,
        'Prague': 4
    }
    
    # Direct flights
    flights = {
        'Reykjavik': ['Stuttgart', 'Vienna', 'Prague'],
        'Stuttgart': ['Reykjavik', 'Split', 'Vienna', 'Edinburgh', 'Manchester'],
        'Vienna': ['Stuttgart', 'Prague', 'Manchester', 'Lyon', 'Split', 'Reykjavik'],
        'Prague': ['Manchester', 'Edinburgh', 'Vienna', 'Split', 'Lyon', 'Reykjavik'],
        'Edinburgh': ['Prague', 'Stuttgart'],
        'Manchester': ['Prague', 'Vienna', 'Split', 'Stuttgart'],
        'Split': ['Stuttgart', 'Manchester', 'Prague', 'Vienna', 'Lyon'],
        'Lyon': ['Vienna', 'Split', 'Prague']
    }
    
    # Fixed constraints
    fixed_events = [
        {'city': 'Edinburgh', 'day_range': (5, 8)},
        {'city': 'Split', 'day_range': (19, 23)}
    ]
    
    total_days = 25
    
    # Generate all possible city orders
    city_names = list(cities.keys())
    possible_orders = permutations(city_names)
    
    valid_itineraries = []
    
    for order in possible_orders:
        itinerary = []
        current_day = 1
        valid = True
        
        # Check fixed events first
        for event in fixed_events:
            event_city = event['city']
            start_day, end_day = event['day_range']
            days_needed = end_day - start_day + 1
            
            # Check if city is in order and days match
            if event_city not in order:
                valid = False
                break
            
            # Find position in order
            pos = order.index(event_city)
            prev_city = order[pos - 1] if pos > 0 else None
            next_city = order[pos + 1] if pos < len(order) - 1 else None
            
            # Check if days can fit
            if cities[event_city] < days_needed:
                valid = False
                break
        
        if not valid:
            continue
        
        # Try to build itinerary
        temp_itinerary = []
        prev_city = None
        remaining_days = cities.copy()
        day_ranges = {}
        
        for city in order:
            if remaining_days[city] <= 0:
                continue
            
            # Check flight connection
            if prev_city and city not in flights[prev_city]:
                valid = False
                break
            
            # Check fixed events
            for event in fixed_events:
                event_city = event['city']
                start_day, end_day = event['day_range']
                
                if city == event_city:
                    # Must be there during the event
                    if current_day > start_day or current_day + remaining_days[city] - 1 < end_day:
                        valid = False
                        break
                    
                    # Adjust days to cover the event
                    days_before = max(0, start_day - current_day)
                    days_during = end_day - start_day + 1
                    days_after = remaining_days[city] - days_before - days_during
                    
                    if days_before > 0:
                        temp_itinerary.append({
                            'day_range': f"Day {current_day}-{current_day + days_before - 1}",
                            'place': city
                        })
                        current_day += days_before
                    
                    temp_itinerary.append({
                        'day_range': f"Day {current_day}-{current_day + days_during - 1}",
                        'place': city
                    })
                    current_day += days_during
                    remaining_days[city] = 0
                    
                    if days_after > 0:
                        temp_itinerary.append({
                            'day_range': f"Day {current_day}-{current_day + days_after - 1}",
                            'place': city
                        })
                        current_day += days_after
                        remaining_days[city] = 0
                    
                    break
            else:
                # No fixed event, just add the days
                temp_itinerary.append({
                    'day_range': f"Day {current_day}-{current_day + remaining_days[city] - 1}",
                    'place': city
                })
                current_day += remaining_days[city]
                remaining_days[city] = 0
            
            prev_city = city
        
        # Check if all days are covered and no overlaps
        if valid and current_day - 1 == total_days and all(v == 0 for v in remaining_days.values()):
            valid_itineraries.append(temp_itinerary)
    
    if not valid_itineraries:
        return {"itinerary": []}
    
    # Select the first valid itinerary (could add optimization here)
    selected_itinerary = valid_itineraries[0]
    
    return {"itinerary": selected_itinerary}

# Run the function and print the result
print(json.dumps(find_itinerary()))