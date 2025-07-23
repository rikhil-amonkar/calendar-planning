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
    cities = list(city_stays.keys())
    for perm in permutations(cities):
        # Check if the permutation respects flight connections
        valid = True
        for i in range(len(perm) - 1):
            if perm[i+1] not in flight_connections[perm[i]]:
                valid = False
                break
        if not valid:
            continue
        
        # Calculate day ranges and check constraints
        itinerary = []
        current_day = 1
        remaining_stays = city_stays.copy()
        
        # Track constraints
        nice_valid = False
        frankfurt_valid = False
        
        for city in perm:
            stay_days = remaining_stays[city]
            day_range = (current_day, current_day + stay_days - 1)
            
            # Check Nice constraint (must be within days 1-5)
            if city == 'Nice':
                if not (day_range[0] >= 1 and day_range[1] <= 5):
                    break  # Nice must be within days 1-5
                nice_valid = True
            
            # Check Frankfurt constraint (must be exactly days 19-20)
            if city == 'Frankfurt':
                if not (day_range[0] == 19 and day_range[1] == 20):
                    break  # Frankfurt must be exactly days 19-20
                frankfurt_valid = True
            
            itinerary.append({
                "day_range": f"Day {day_range[0]}-{day_range[1]}",
                "place": city
            })
            current_day += stay_days
        
        # Check if all constraints are met
        if (current_day - 1 == total_days and 
            nice_valid and frankfurt_valid):
            return {"itinerary": itinerary}
    
    return {"itinerary": []}  # Fallback if no valid itinerary found

if __name__ == "__main__":
    itinerary = find_itinerary()
    print(json.dumps(itinerary, indent=2))