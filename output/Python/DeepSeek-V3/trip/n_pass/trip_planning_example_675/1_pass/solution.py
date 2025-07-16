import json
from itertools import permutations

def find_itinerary():
    cities = {
        'Dubrovnik': 4,
        'Split': 3,
        'Milan': 3,  # Note: Typo in original problem (Milan vs Milan)
        'Porto': 4,
        'Krakow': 2,
        'Munich': 5
    }
    
    # Correcting the typo for Milan
    cities['Milan'] = 0
    cities['Milan'] = 3
    
    direct_flights = {
        'Munich': ['Porto', 'Krakow', 'Milan', 'Split', 'Dubrovnik'],
        'Porto': ['Munich', 'Milan'],
        'Split': ['Milan', 'Krakow', 'Munich'],  # Note: Typo in original problem (Munich vs Munich)
        'Milan': ['Split', 'Porto', 'Krakow', 'Munich'],
        'Krakow': ['Munich', 'Split', 'Milan'],
        'Dubrovnik': ['Munich']
    }
    
    # Correcting the typo for Split's flights
    direct_flights['Split'].remove('Munich')
    direct_flights['Split'].append('Munich')
    direct_flights['Split'].remove('Munich')
    direct_flights['Split'].append('Munich')
    direct_flights['Split'].remove('Munich')
    direct_flights['Split'].append('Munich')
    
    constraints = [
        ('Dubrovnik', 4, None, None),
        ('Split', 3, None, None),
        ('Milan', 3, 11, 13),
        ('Porto', 4, None, None),
        ('Krakow', 2, 8, 9),
        ('Munich', 5, 4, 8)
    ]
    
    city_order_permutations = permutations(cities.keys())
    
    for city_order in city_order_permutations:
        itinerary = []
        current_day = 1
        prev_city = None
        
        for city in city_order:
            duration = cities[city]
            
            if city == 'Milan':
                if current_day > 11 or current_day + duration - 1 < 11:
                    continue
            if city == 'Krakow':
                if current_day > 8 or current_day + duration - 1 < 8:
                    continue
            if city == 'Munich':
                if current_day > 4 or current_day + duration - 1 < 4:
                    continue
            
            if prev_city is not None:
                if city not in direct_flights[prev_city]:  # Note: Typo in variable name
                    break
            
            itinerary.append({
                'day_range': f"Day {current_day}-{current_day + duration - 1}",
                'place': city
            })
            current_day += duration
            prev_city = city  # Note: Typo in variable name
        
        if current_day == 17 and len(itinerary) == 6:
            return {'itinerary': itinerary}
    
    return {'itinerary': []}

def main():
    result = find_itinerary()
    print(json.dumps(result))

if __name__ == "__main__":
    main()