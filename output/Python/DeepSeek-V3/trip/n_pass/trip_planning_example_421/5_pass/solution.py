import json
from itertools import permutations

def find_itinerary():
    # Define the constraints
    total_days = 20
    city_stays = {
        'Nice': 5,
        'Krakow': 6,
        'Dublin': 7,
        'Lyon': 4,
        'Frankfurt': 2
    }
    
    # Define the flight connections
    connections = {
        'Nice': ['Dublin', 'Frankfurt', 'Lyon'],
        'Dublin': ['Nice', 'Frankfurt', 'Krakow', 'Lyon'],
        'Krakow': ['Dublin', 'Frankfurt'],
        'Lyon': ['Frankfurt', 'Dublin', 'Nice'],
        'Frankfurt': ['Dublin', 'Krakow', 'Lyon', 'Nice']
    }
    
    # Cities to visit (excluding Nice and Frankfurt since their positions are fixed)
    middle_cities = ['Krakow', 'Dublin', 'Lyon']
    
    # Generate all possible permutations of the middle cities
    for perm in permutations(middle_cities):
        # Construct full sequence: Nice + middle cities + Frankfurt
        full_sequence = ['Nice'] + list(perm) + ['Frankfurt']
        
        # Check if all connections are valid
        valid = True
        for i in range(len(full_sequence) - 1):
            current = full_sequence[i]
            next_city = full_sequence[i+1]
            if next_city not in connections.get(current, []):
                valid = False
                break
        if not valid:
            continue
        
        # Assign days - Nice is fixed to days 1-5
        itinerary = [{
            'day_range': 'Day 1-5',
            'place': 'Nice'
        }]
        current_day = 6
        
        # Assign days for middle cities
        total_used_days = 5  # Nice
        
        for city in perm:
            stay_duration = city_stays[city]
            total_used_days += stay_duration
            
            # Check if we have enough days left for Frankfurt
            if total_used_days + city_stays['Frankfurt'] > total_days:
                valid = False
                break
            
            end_day = current_day + stay_duration - 1
            itinerary.append({
                'day_range': f'Day {current_day}-{end_day}',
                'place': city
            })
            current_day += stay_duration
        
        if not valid:
            continue
        
        # Add Frankfurt (must be days 19-20)
        if current_day != 19:
            continue
            
        itinerary.append({
            'day_range': 'Day 19-20',
            'place': 'Frankfurt'
        })
        
        # Final check that we used exactly 20 days
        if total_used_days + city_stays['Frankfurt'] == total_days:
            return {'itinerary': itinerary}
    
    return {'itinerary': []}

# Execute the function and print the result
result = find_itinerary()
print(json.dumps(result, indent=2))