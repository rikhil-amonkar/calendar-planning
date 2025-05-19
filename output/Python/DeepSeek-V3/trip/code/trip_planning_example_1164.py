import json
from itertools import permutations

def find_itinerary():
    # Define cities and their constraints
    cities = {
        'Reykjavik': {'duration': 2, 'constraints': [{'type': 'meet', 'day_range': (3, 4)}]},
        'Stockholm': {'duration': 2, 'constraints': [{'type': 'meet', 'day_range': (4, 5)}]},
        'Porto': {'duration': 5, 'constraints': [{'type': 'wedding', 'day_range': (13, 17)}]},
        'Nice': {'duration': 3, 'constraints': []},
        'Venice': {'duration': 4, 'constraints': []},
        'Vienna': {'duration': 3, 'constraints': [{'type': 'workshop', 'day_range': (11, 13)}]},
        'Split': {'duration': 3, 'constraints': []},
        'Copenhagen': {'duration': 2, 'constraints': []}
    }
    
    # Define direct flight connections
    direct_flights = {
        'Copenhagen': ['Vienna', 'Nice', 'Split', 'Reykjavik', 'Venice', 'Porto', 'Stockholm'],
        'Vienna': ['Copenhagen', 'Nice', 'Reykjavik', 'Venice', 'Porto', 'Stockholm', 'Split'],
        'Nice': ['Stockholm', 'Reykjavik', 'Porto', 'Venice', 'Vienna', 'Copenhagen'],
        'Split': ['Copenhagen', 'Stockholm', 'Vienna'],
        'Reykjavik': ['Nice', 'Vienna', 'Copenhagen', 'Stockholm'],
        'Stockholm': ['Nice', 'Copenhagen', 'Split', 'Vienna', 'Reykjavik'],
        'Venice': ['Nice', 'Vienna', 'Copenhagen'],
        'Porto': ['Nice', 'Copenhagen', 'Vienna']
    }
    
    # Check if a flight exists between two cities
    def has_flight(a, b):
        return b in direct_flights.get(a, [])
    
    # Generate all possible permutations of cities
    for perm in permutations(cities.keys()):
        itinerary = []
        current_day = 1
        valid = True
        
        # Check if the permutation satisfies all constraints
        for i in range(len(perm)):
            city = perm[i]
            duration = cities[city]['duration']
            end_day = current_day + duration - 1
            
            # Check constraints for the city
            for constraint in cities[city]['constraints']:
                if constraint['type'] == 'meet':
                    if not (current_day <= constraint['day_range'][0] and end_day >= constraint['day_range'][1] - 1):
                        valid = False
                        break
                elif constraint['type'] == 'wedding':
                    if not (current_day <= constraint['day_range'][0] and end_day >= constraint['day_range'][1] - 1):
                        valid = False
                        break
                elif constraint['type'] == 'workshop':
                    if not (current_day <= constraint['day_range'][0] and end_day >= constraint['day_range'][1] - 1):
                        valid = False
                        break
            if not valid:
                break
            
            # Add to itinerary
            itinerary.append({
                'day_range': f'Day {current_day}-{end_day}',
                'place': city
            })
            
            # Check flight to next city
            if i < len(perm) - 1:
                next_city = perm[i + 1]
                if not has_flight(city, next_city):
                    valid = False
                    break
                itinerary.append({
                    'flying': f'Day {end_day}-{end_day}',
                    'from': city,
                    'to': next_city
                })
                current_day = end_day + 1
        
        # Check if total days match and all constraints are satisfied
        if valid and current_day - 1 == 17:
            return itinerary
    
    return None

def main():
    itinerary = find_itinerary()
    if itinerary:
        print(json.dumps(itinerary, indent=2))
    else:
        print(json.dumps({"error": "No valid itinerary found"}, indent=2))

if __name__ == "__main__":
    main()