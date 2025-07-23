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
    
    flight_connections = {
        'Nice': ['Dublin', 'Frankfurt', 'Lyon'],
        'Dublin': ['Nice', 'Frankfurt', 'Krakow', 'Lyon'],
        'Krakow': ['Dublin', 'Frankfurt'],
        'Frankfurt': ['Dublin', 'Krakow', 'Lyon', 'Nice'],
        'Lyon': ['Frankfurt', 'Dublin', 'Nice']
    }
    
    # Generate all possible city orders (permutations)
    cities = [c for c in city_stays.keys() if c not in ['Nice', 'Frankfurt']]
    
    # Nice must be first (days 1-5) and Frankfurt must be last (days 19-20)
    # So we only need to permute the middle cities (Krakow, Dublin, Lyon)
    for middle_perm in permutations(cities):
        perm = ['Nice'] + list(middle_perm) + ['Frankfurt']
        
        # Check flight connections
        valid = True
        for i in range(len(perm) - 1):
            if perm[i+1] not in flight_connections[perm[i]]:
                valid = False
                break
        if not valid:
            continue
        
        # Calculate day ranges
        itinerary = []
        current_day = 1
        
        for city in perm:
            stay_days = city_stays[city]
            day_range = (current_day, current_day + stay_days - 1)
            
            itinerary.append({
                "day_range": f"Day {day_range[0]}-{day_range[1]}",
                "place": city
            })
            current_day += stay_days
        
        # Verify total days and Frankfurt position
        if current_day - 1 == total_days:
            return {"itinerary": itinerary}
    
    return {"itinerary": []}  # Fallback if no valid itinerary found

if __name__ == "__main__":
    itinerary = find_itinerary()
    print(json.dumps(itinerary, indent=2))