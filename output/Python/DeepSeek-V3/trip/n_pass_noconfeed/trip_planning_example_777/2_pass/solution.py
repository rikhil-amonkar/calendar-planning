import json
from itertools import permutations

def find_itinerary():
    # Cities and required days
    cities = {
        'Dublin': 5,
        'Helsinki': 3,
        'Riga': 3,
        'Reykjavik': 2,
        'Vienna': 2,
        'Tallinn': 5
    }
    
    # Direct flights
    direct_flights = {
        'Helsinki': ['Riga', 'Dublin', 'Tallinn', 'Reykjavik'],
        'Riga': ['Helsinki', 'Tallinn', 'Vienna', 'Dublin'],
        'Vienna': ['Riga', 'Dublin', 'Reykjavik'],
        'Reykjavik': ['Vienna', 'Helsinki', 'Dublin'],
        'Tallinn': ['Dublin', 'Helsinki', 'Riga'],
        'Dublin': ['Helsinki', 'Riga', 'Tallinn', 'Vienna', 'Reykjavik']
    }
    
    # Constraints
    constraints = {
        'Helsinki': (3, 5),  # Helsinki between day 3-5
        'Vienna': (2, 3),    # Vienna between day 2-3
        'Tallinn': (7, 11)   # Tallinn between day 7-11
    }
    
    total_days = 15
    
    # We'll use a more targeted approach rather than all permutations
    # Let's try to satisfy constraints first
    
    # Try starting with Vienna (since it has earliest constraint)
    for start_city in ['Vienna']:
        for perm in permutations([c for c in cities if c != start_city]):
            itinerary = []
            current_day = 1
            valid = True
            
            # Create the full sequence with start_city first
            sequence = [start_city] + list(perm)
            
            # Assign days to each city in sequence
            temp_itinerary = []
            remaining_days = {city: cities[city] for city in cities}
            prev_city = None
            
            for city in sequence:
                if current_day > total_days:
                    valid = False
                    break
                
                days_needed = cities[city]
                end_day = current_day + days_needed - 1
                
                if end_day > total_days:
                    valid = False
                    break
                
                # Check flight connection
                if prev_city is not None and city not in direct_flights[prev_city]:
                    valid = False
                    break
                
                temp_itinerary.append({
                    'city': city,
                    'start_day': current_day,
                    'end_day': end_day
                })
                
                current_day = end_day + 1
                prev_city = city
            
            # Check if all days are assigned and all cities are covered
            if not valid or current_day <= total_days + 1:
                continue
            
            # Check constraints
            constraint_met = True
            for const_city, (start, end) in constraints.items():
                found = False
                for entry in temp_itinerary:
                    if entry['city'] == const_city:
                        # Check if the city's stay is completely within constraint days
                        if (entry['start_day'] >= start and entry['end_day'] <= end):
                            found = True
                            break
                        # Or at least partially overlaps (depending on interpretation)
                        elif not (entry['end_day'] < start or entry['start_day'] > end):
                            found = True
                            break
                if not found:
                    constraint_met = False
                    break
            
            if constraint_met:
                itinerary = temp_itinerary
                break
        
        if itinerary:
            break
    
    if not itinerary:
        return {"itinerary": []}
    
    # Format the itinerary
    formatted_itinerary = []
    for entry in itinerary:
        if entry['start_day'] == entry['end_day']:
            day_range = f"Day {entry['start_day']}"
        else:
            day_range = f"Day {entry['start_day']}-{entry['end_day']}"
        formatted_itinerary.append({
            "day_range": day_range,
            "place": entry['city']
        })
    
    return {"itinerary": formatted_itinerary}

# Execute and print the result
result = find_itinerary()
print(json.dumps(result, indent=2))