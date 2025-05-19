import json
from itertools import permutations

def find_itinerary():
    # Parameters
    total_days = 26
    cities = {
        'Venice': 4,
        'Barcelona': 3,
        'Copenhagen': 4,
        'Lyon': 4,
        'Reykjavik': 4,
        'Dubrovnik': 5,
        'Athens': 2,
        'Tallinn': 5,
        'Munich': 3
    }
    constraints = {
        'Barcelona': {'meet_friend': (10, 12)},
        'Copenhagen': {'visit_relatives': (7, 10)},
        'Dubrovnik': {'wedding': (16, 20)}
    }
    
    # Direct flights
    direct_flights = {
        'Copenhagen': ['Athens', 'Dubrovnik', 'Munich', 'Reykjavik', 'Barcelona', 'Tallinn', 'Venice'],
        'Munich': ['Tallinn', 'Copenhagen', 'Venice', 'Reykjavik', 'Athens', 'Lyon', 'Dubrovnik', 'Barcelona'],
        'Venice': ['Munich', 'Athens', 'Lyon', 'Barcelona', 'Copenhagen'],
        'Reykjavik': ['Athens', 'Copenhagen', 'Munich', 'Barcelona'],
        'Athens': ['Copenhagen', 'Dubrovnik', 'Venice', 'Reykjavik', 'Munich', 'Barcelona'],
        'Lyon': ['Barcelona', 'Munich', 'Venice'],
        'Barcelona': ['Lyon', 'Dubrovnik', 'Athens', 'Reykjavik', 'Copenhagen', 'Venice', 'Munich', 'Tallinn'],
        'Dubrovnik': ['Copenhagen', 'Athens', 'Barcelona', 'Munich'],
        'Tallinn': ['Munich', 'Barcelona', 'Copenhagen']
    }
    
    # All cities to visit
    cities_to_visit = list(cities.keys())
    
    # Generate all possible permutations of cities
    for perm in permutations(cities_to_visit):
        itinerary = []
        current_day = 1
        valid = True
        
        # Check if the permutation satisfies all constraints
        for i, city in enumerate(perm):
            stay_days = cities[city]
            day_start = current_day
            day_end = current_day + stay_days - 1
            
            # Check constraints for the city
            if city in constraints:
                for constraint, (start, end) in constraints[city].items():
                    if not (day_start <= end and day_end >= start):
                        valid = False
                        break
                if not valid:
                    break
            
            # Add to itinerary
            itinerary.append({
                'day_range': f'Day {day_start}-{day_end}',
                'place': city
            })
            
            # Check if not the last city
            if i < len(perm) - 1:
                next_city = perm[i+1]
                if next_city not in direct_flights.get(city, []):
                    valid = False
                    break
                
                # Add flight day
                itinerary.append({
                    'flying': f'Day {day_end}-{day_end}',
                    'from': city,
                    'to': next_city
                })
            
            current_day = day_end + 1
        
        # Check if total days match and itinerary is valid
        if valid and current_day - 1 == total_days:
            return itinerary
    
    return None

itinerary = find_itinerary()
if itinerary:
    print(json.dumps(itinerary, indent=2))
else:
    print(json.dumps({"error": "No valid itinerary found"}, indent=2))