import json
from itertools import permutations

def main():
    # Input parameters
    cities = {
        'Istanbul': 4,
        'Vienna': 4,
        'Riga': 2,
        'Brussels': 2,  # Typo in original, but kept as 'Brussels' is used elsewhere
        'Madrid': 4,
        'Vilnius': 4,
        'Venice': 5,
        'Geneva': 4,
        'Munich': 5,
        'Reykjavik': 2
    }
    
    constraints = [
        {'city': 'Brussels', 'day_range': (26, 27)},
        {'city': 'Vilnius', 'day_range': (20, 23)},
        {'city': 'Venice', 'day_range': (7, 11)},
        {'city': 'Geneva', 'day_range': (1, 4)}
    ]
    
    direct_flights = {
        'Munich': ['Vienna', 'Madrid', 'Venice', 'Reykjavik', 'Istanbul', 'Brussels', 'Riga'],
        'Vienna': ['Munich', 'Vilnius', 'Istanbul', 'Venice', 'Reykjavik', 'Riga', 'Brussels', 'Geneva', 'Madrid'],
        'Istanbul': ['Brussels', 'Geneva', 'Vienna', 'Riga', 'Venice', 'Munich', 'Vilnius', 'Madrid'],
        'Brussels': ['Istanbul', 'Venice', 'Riga', 'Reykjavik', 'Vilnius', 'Vienna', 'Madrid', 'Geneva', 'Munich'],
        'Madrid': ['Munich', 'Venice', 'Vienna', 'Geneva', 'Brussels', 'Istanbul'],
        'Vilnius': ['Vienna', 'Istanbul', 'Brussels', 'Munich', 'Riga'],
        'Venice': ['Brussels', 'Munich', 'Madrid', 'Vienna', 'Istanbul'],
        'Geneva': ['Istanbul', 'Vienna', 'Brussels', 'Madrid', 'Munich'],
        'Riga': ['Brussels', 'Istanbul', 'Munich', 'Vilnius', 'Vienna'],
        'Reykjavik': ['Munich', 'Vienna', 'Brussels', 'Madrid']
    }
    
    # Generate all possible city orders (permutations)
    city_names = list(cities.keys())
    possible_orders = permutations(city_names)
    
    # Function to check if a flight is possible
    def can_fly(from_city, to_city):
        return to_city in direct_flights.get(from_city, [])
    
    # Function to check if constraints are satisfied
    def satisfies_constraints(itinerary):
        for constraint in constraints:
            city = constraint['city']
            day_start, day_end = constraint['day_range']
            found = False
            current_day = 1
            for entry in itinerary:
                if 'place' in entry:
                    place = entry['place']
                    day_range = entry['day_range']
                    start_day = int(day_range.split('-')[0][4:])
                    end_day = int(day_range.split('-')[1])
                    if place == city:
                        if start_day <= day_end and end_day >= day_start:
                            found = True
                            break
                    current_day = end_day + 1
                else:
                    current_day += 1
            if not found:
                return False
        return True
    
    # Function to generate itinerary for a given order
    def generate_itinerary(order):
        itinerary = []
        current_day = 1
        prev_city = None
        
        for city in order:
            if prev_city is not None and prev_city != city:
                if not can_fly(prev_city, city):
                    return None
                itinerary.append({
                    'flying': f'Day {current_day}-{current_day}',
                    'from': prev_city,
                    'to': city
                })
                current_day += 1  # Travel day
            
            stay_days = cities[city]
            end_day = current_day + stay_days - 1
            itinerary.append({
                'day_range': f'Day {current_day}-{end_day}',
                'place': city
            })
            current_day = end_day + 1
            prev_city = city
        
        # Check total days
        total_days = 0
        for entry in itinerary:
            if 'day_range' in entry:
                start, end = map(int, entry['day_range'].split('-')[0][4:], entry['day_range'].split('-')[1])
                total_days += end - start + 1
            else:
                total_days += 1
        
        if total_days != 27:
            return None
        
        if not satisfies_constraints(itinerary):
            return None
        
        return itinerary
    
    # Try possible orders until a valid itinerary is found
    valid_itinerary = None
    for order in possible_orders:
        itinerary = generate_itinerary(order)
        if itinerary is not None:
            valid_itinerary = itinerary
            break
    
    # Output the result
    print(json.dumps(valid_itinerary, indent=2))

if __name__ == "__main__":
    main()