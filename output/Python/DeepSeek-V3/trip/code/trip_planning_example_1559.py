import json
from itertools import permutations

def main():
    # Cities and their required days
    cities = {
        'Valencia': 2,
        'Oslo': 3,
        'Lyon': 4,
        'Prague': 3,
        'Paris': 4,
        'Nice': 4,
        'Seville': 5,
        'Tallinn': 2,
        'Mykonos': 5,
        'Lisbon': 2
    }
    
    # Direct flights
    direct_flights = {
        'Lisbon': ['Paris', 'Seville', 'Prague', 'Valencia', 'Nice', 'Oslo', 'Lyon'],
        'Paris': ['Lisbon', 'Oslo', 'Valencia', 'Nice', 'Lyon', 'Tallinn', 'Prague', 'Seville'],
        'Lyon': ['Nice', 'Prague', 'Paris', 'Valencia', 'Oslo'],
        'Nice': ['Lyon', 'Paris', 'Mykonos', 'Lisbon', 'Oslo'],
        'Oslo': ['Tallinn', 'Paris', 'Prague', 'Nice', 'Lyon', 'Lisbon'],
        'Prague': ['Lyon', 'Lisbon', 'Oslo', 'Paris', 'Valencia', 'Tallinn'],
        'Seville': ['Lisbon', 'Paris', 'Valencia'],
        'Tallinn': ['Oslo', 'Paris', 'Prague'],
        'Mykonos': ['Nice'],
        'Valencia': ['Paris', 'Lisbon', 'Lyon', 'Prague', 'Seville']
    }
    
    # Constraints
    constraints = [
        {'city': 'Valencia', 'day_range': (3, 4)},
        {'city': 'Seville', 'day_range': (5, 9)},
        {'city': 'Oslo', 'day_range': (13, 15)},
        {'city': 'Mykonos', 'day_range': (21, 25)}
    ]
    
    # Generate all possible permutations of cities
    city_names = list(cities.keys())
    all_permutations = permutations(city_names)
    
    def is_valid_route(route):
        # Check if all constraints are met
        day = 1
        itinerary = []
        for i, city in enumerate(route):
            stay_days = cities[city]
            end_day = day + stay_days - 1
            itinerary.append({'city': city, 'start': day, 'end': end_day})
            
            # Check constraints
            for constraint in constraints:
                if constraint['city'] == city:
                    if not (constraint['day_range'][0] <= day <= constraint['day_range'][1] or 
                           constraint['day_range'][0] <= end_day <= constraint['day_range'][1] or 
                           (day <= constraint['day_range'][0] and end_day >= constraint['day_range'][1])):
                        return False
            
            day = end_day + 1
            if i < len(route) - 1:
                next_city = route[i+1]
                if next_city not in direct_flights[city]:
                    return False
        return day - 1 <= 25
    
    # Find a valid route
    valid_route = None
    for perm in all_permutations:
        if is_valid_route(perm):
            valid_route = perm
            break
    
    if not valid_route:
        print(json.dumps({"error": "No valid itinerary found"}))
        return
    
    # Generate itinerary
    day = 1
    itinerary = []
    for i, city in enumerate(valid_route):
        stay_days = cities[city]
        end_day = day + stay_days - 1
        itinerary.append({'day_range': f'Day {day}-{end_day}', 'place': city})
        
        if i < len(valid_route) - 1:
            next_city = valid_route[i+1]
            itinerary.append({'flying': f'Day {end_day+1}-{end_day+1}', 'from': city, 'to': next_city})
            day = end_day + 1
        else:
            day = end_day + 1
    
    print(json.dumps(itinerary, indent=2))

if __name__ == "__main__":
    main()