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
    
    # Try all possible permutations of cities
    for perm in permutations(cities.keys()):
        itinerary = []
        current_day = 1
        valid = True
        prev_city = None
        
        temp_itinerary = []
        
        for city in perm:
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
        
        # Check if all cities are covered and all days used (exactly 15 days)
        if not valid or current_day - 1 != total_days:
            continue
        
        # Check constraints
        constraint_met = True
        for const_city, (start, end) in constraints.items():
            found = False
            for entry in temp_itinerary:
                if entry['city'] == const_city:
                    # Check if the entire stay is within constraint days
                    if entry['start_day'] >= start and entry['end_day'] <= end:
                        found = True
                        break
            if not found:
                constraint_met = False
                break
        
        if constraint_met:
            itinerary = temp_itinerary
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