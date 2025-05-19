import json
from itertools import permutations

def main():
    # Input parameters
    total_days = 32
    cities = {
        'Bucharest': 2,
        'Krakow': 4,
        'Munich': 3,
        'Barcelona': 5,
        'Warsaw': 5,
        'Budapest': 5,
        'Stockholm': 2,
        'Riga': 5,
        'Edinburgh': 5,
        'Vienna': 5
    }
    
    # Constraints
    constraints = [
        {'place': 'Munich', 'day_range': (18, 20)},
        {'place': 'Warsaw', 'day_range': (25, 29)},
        {'place': 'Budapest', 'day_range': (9, 13)},
        {'place': 'Stockholm', 'day_range': (17, 18)},
        {'place': 'Edinburgh', 'day_range': (1, 5)}
    ]
    
    # Direct flights
    direct_flights = {
        'Budapest': ['Munich', 'Vienna', 'Edinburgh', 'Warsaw', 'Barcelona', 'Bucharest'],
        'Bucharest': ['Riga', 'Munich', 'Warsaw', 'Vienna', 'Barcelona', 'Budapest'],
        'Munich': ['Budapest', 'Krakow', 'Warsaw', 'Bucharest', 'Barcelona', 'Stockholm', 'Edinburgh', 'Vienna', 'Riga'],
        'Krakow': ['Munich', 'Warsaw', 'Edinburgh', 'Stockholm', 'Vienna', 'Barcelona'],
        'Barcelona': ['Warsaw', 'Munich', 'Stockholm', 'Edinburgh', 'Riga', 'Budapest', 'Bucharest', 'Krakow', 'Vienna'],
        'Warsaw': ['Munich', 'Barcelona', 'Krakow', 'Bucharest', 'Vienna', 'Budapest', 'Riga', 'Stockholm'],
        'Stockholm': ['Edinburgh', 'Krakow', 'Munich', 'Barcelona', 'Riga', 'Vienna', 'Warsaw'],
        'Riga': ['Bucharest', 'Barcelona', 'Edinburgh', 'Vienna', 'Munich', 'Warsaw', 'Stockholm'],
        'Edinburgh': ['Stockholm', 'Krakow', 'Barcelona', 'Budapest', 'Munich', 'Riga'],
        'Vienna': ['Budapest', 'Bucharest', 'Krakow', 'Munich', 'Stockholm', 'Riga', 'Warsaw', 'Barcelona']
    }
    
    # Generate all possible city orders that meet constraints
    def is_valid_order(order):
        # Check if all constraints are met in the order
        constraint_places = {c['place'] for c in constraints}
        # All constrained cities must be in the order
        if not all(city in order for city in constraint_places):
            return False
        
        # Check if the order can satisfy the day constraints
        day = 1
        for i in range(len(order)):
            city = order[i]
            stay = cities[city]
            end_day = day + stay - 1
            
            # Check constraints for this city
            for constr in constraints:
                if constr['place'] == city:
                    constr_start, constr_end = constr['day_range']
                    if not (day <= constr_start and end_day >= constr_end):
                        return False
            
            day = end_day + 1
            if i < len(order) - 1:
                day += 1  # flight day
        
        return day - 1 <= total_days
    
    # Try to find a valid order
    valid_order = None
    for perm in permutations(cities.keys()):
        if is_valid_order(perm):
            valid_order = perm
            break
    
    if not valid_order:
        print(json.dumps({"error": "No valid itinerary found"}))
        return
    
    # Build itinerary
    itinerary = []
    day = 1
    for i in range(len(valid_order)):
        city = valid_order[i]
        stay = cities[city]
        end_day = day + stay - 1
        
        # Add stay
        itinerary.append({
            'day_range': f'Day {day}-{end_day}',
            'place': city
        })
        
        day = end_day + 1
        if i < len(valid_order) - 1:
            next_city = valid_order[i+1]
            # Add flight
            itinerary.append({
                'flying': f'Day {day}-{day}',
                'from': city,
                'to': next_city
            })
            day += 1
    
    print(json.dumps(itinerary, indent=2))

if __name__ == "__main__":
    main()