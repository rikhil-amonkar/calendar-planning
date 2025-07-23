import json
from itertools import permutations

def find_itinerary():
    cities = {
        'Vienna': 4,
        'Milan': 2,
        'Rome': 3,
        'Riga': 2,
        'Lisbon': 3,
        'Vilnius': 4,
        'Oslo': 3
    }
    
    constraints = {
        'Vienna': [(1, 1), (4, 4)],
        'Lisbon': [(11, 13)],
        'Oslo': [(13, 15)]
    }
    
    flight_routes = {
        'Riga': ['Oslo', 'Rome', 'Milan', 'Vienna', 'Lisbon', 'Vilnius'],
        'Oslo': ['Riga', 'Rome', 'Lisbon', 'Milan', 'Vienna', 'Vilnius'],
        'Rome': ['Oslo', 'Riga', 'Lisbon', 'Vienna'],
        'Milan': ['Vienna', 'Riga', 'Oslo', 'Lisbon', 'Vilnius'],
        'Vienna': ['Milan', 'Vilnius', 'Lisbon', 'Riga', 'Rome', 'Oslo'],
        'Vilnius': ['Vienna', 'Oslo', 'Riga', 'Milan'],
        'Lisbon': ['Vienna', 'Oslo', 'Rome', 'Milan', 'Riga']
    }
    
    # Correcting city name inconsistencies and flight routes
    flight_routes['Vienna'].remove('Milan')
    flight_routes['Milan'].remove('Vienna')
    flight_routes['Milan'].append('Vienna')
    flight_routes['Lisbon'].remove('Milan')
    flight_routes['Lisbon'].append('Milan')
    
    # Generate all possible city orders
    city_list = list(cities.keys())
    possible_orders = permutations(city_list)
    
    valid_itineraries = []
    
    for order in possible_orders:
        itinerary = []
        current_city = None
        remaining_days = cities.copy()
        day = 1
        valid = True
        
        for city in order:
            if current_city is None:
                current_city = city
            else:
                if city not in flight_routes[current_city]:
                    valid = False
                    break
                current_city = city
            
            # Check constraints for current city
            if current_city in constraints:
                for (start, end) in constraints[current_city]:
                    if day > end or (day + remaining_days[current_city] - 1) < start:
                        valid = False
                        break
                if not valid:
                    break
            
            # Allocate days to current city
            days_to_spend = remaining_days[current_city]
            itinerary.append({'day_range': f'Day {day}-{day + days_to_spend - 1}', 'place': current_city})
            day += days_to_spend
            remaining_days[current_city] = 0
            
            if day > 15:
                valid = False
                break
        
        if valid and day == 16 and all(days == 0 for days in remaining_days.values()):
            valid_itineraries.append(itinerary)
    
    if not valid_itineraries:
        return {"itinerary": []}
    
    # Select the first valid itinerary (could be optimized further)
    return {"itinerary": valid_itineraries[0]}

result = find_itinerary()
print(json.dumps(result))