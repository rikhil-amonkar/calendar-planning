import json
from itertools import permutations

def find_itinerary():
    # Define the constraints
    total_days = 9
    city_stays = {
        'Nice': 2,
        'Stockholm': 5,
        'Split': 3,
        'Vienna': 2
    }
    
    # Conference and workshop constraints
    conference_days = {7, 9}  # Must be in Split on these days
    workshop_days = {1, 2}    # Must be in Vienna on at least one of these days
    
    # Direct flights adjacency list
    flights = {
        'Vienna': ['Stockholm', 'Nice', 'Split'],
        'Stockholm': ['Vienna', 'Nice', 'Split'],
        'Nice': ['Vienna', 'Stockholm'],
        'Split': ['Vienna', 'Stockholm']
    }
    
    # Generate all possible city visit orders (permutations)
    cities = list(city_stays.keys())
    possible_orders = permutations(cities)
    
    # Check each possible order for validity
    for order in possible_orders:
        itinerary = []
        remaining_stays = city_stays.copy()
        day = 1
        temp_itinerary = []
        valid = True
        
        # Track which city we're in each day
        day_to_city = {}
        
        # Assign stays to days
        for city in order:
            if day > total_days:
                break
                
            stay = remaining_stays[city]
            start_day = day
            end_day = day + stay - 1
            
            if end_day > total_days:
                valid = False
                break
                
            # Check flight connectivity with previous city (if not first city)
            if len(temp_itinerary) > 0:
                prev_city = temp_itinerary[-1]['place']
                if city not in flights[prev_city]:
                    valid = False
                    break
            
            temp_itinerary.append({
                'day_range': f"Day {start_day}-{end_day}",
                'place': city
            })
            
            # Record which city is visited each day
            for d in range(start_day, end_day + 1):
                day_to_city[d] = city
                
            remaining_stays[city] = 0
            day = end_day + 1
        
        # Check if all stays are allocated and all days are filled
        if not all(v == 0 for v in remaining_stays.values()) or day <= total_days:
            valid = False
        
        # Check conference and workshop constraints
        if valid:
            # Check conference days (must be in Split on days 7 and 9)
            if not all(day_to_city.get(d) == 'Split' for d in conference_days):
                valid = False
            
            # Check workshop day (must be in Vienna on at least one of days 1 or 2)
            if not any(day_to_city.get(d) == 'Vienna' for d in workshop_days):
                valid = False
        
        if valid:
            itinerary = temp_itinerary
            break
    
    if not itinerary:
        return {"error": "No valid itinerary found"}
    
    return {"itinerary": itinerary}

# Execute and print the result
result = find_itinerary()
print(json.dumps(result, indent=2))