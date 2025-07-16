import json
from itertools import permutations

def find_itinerary():
    # Cities and required days
    cities = {
        'Helsinki': 4,
        'Valencia': 5,
        'Dubrovnik': 4,
        'Porto': 3,
        'Prague': 3,
        'Reykjavik': 4
    }
    
    # Direct flights
    direct_flights = {
        'Helsinki': ['Prague', 'Reykjavik', 'Dubrovnik'],
        'Prague': ['Helsinki', 'Valencia', 'Reykjavik'],
        'Valencia': ['Prague', 'Porto'],
        'Porto': ['Valencia'],
        'Reykjavik': ['Helsinki', 'Prague'],
        'Dubrovnik': ['Helsinki']
    }
    
    # Correcting typo in city names
    direct_flights['Helsinki'].remove('Prague')
    direct_flights['Helsinki'] = ['Prague', 'Reykjavik', 'Dubrovnik']
    direct_flights['Prague'].remove('Helsinki')
    direct_flights['Prague'].append('Helsinki')
    direct_flights['Porto'] = direct_flights.pop('Porto', ['Valencia'])
    direct_flights['Porto'] = ['Valencia']
    direct_flights['Porto'] = ['Valencia']
    
    # Porto must be between day 16 and 18 (inclusive)
    # So Porto must be the last city or second last with days overlapping into last days
    
    # Generate all possible permutations of the cities
    city_names = list(cities.keys())
    possible_orders = permutations(city_names)
    
    valid_itineraries = []
    
    for order in possible_orders:
        # Check if flights are possible between consecutive cities
        valid_order = True
        for i in range(len(order) - 1):
            current_city = order[i]
            next_city = order[i+1]
            if next_city not in direct_flights.get(current_city, []):
                valid_order = False
                break
        if not valid_order:
            continue
        
        # Check if Porto is at the end (last or second last with overlap)
        porto_index = order.index('Porto')
        days_before_porto = sum(cities[city] for city in order[:porto_index])
        porto_days = cities['Porto']
        porto_start_day = days_before_porto + 1
        porto_end_day = porto_start_day + porto_days - 1
        
        if not (16 <= porto_start_day <= 18 or 16 <= porto_end_day <= 18 or (porto_start_day <= 16 and porto_end_day >= 18)):
            continue
        
        # Check total days
        total_days = sum(cities.values())
        if total_days != 18:
            continue  # though this should always be 18 based on the input
        
        # Build itinerary
        itinerary = []
        current_day = 1
        for city in order:
            days = cities[city]
            end_day = current_day + days - 1
            itinerary.append({
                'day_range': f"Day {current_day}-{end_day}",
                'place': city
            })
            current_day = end_day + 1
        
        valid_itineraries.append(itinerary)
    
    if not valid_itineraries:
        return {"itinerary": []}
    
    # Select the first valid itinerary (can be optimized further if needed)
    selected_itinerary = valid_itineraries[0]
    
    return {"itinerary": selected_itinerary}

# Execute and print the result
result = find_itinerary()
print(json.dumps(result, indent=2))