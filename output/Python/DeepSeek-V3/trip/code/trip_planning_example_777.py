import json
from itertools import permutations

def find_itinerary():
    # Cities and their required days
    cities = {
        'Dublin': 5,
        'Helsinki': 3,
        'Riga': 3,
        'Reykjavik': 2,
        'Vienna': 2,
        'Tallinn': 5
    }
    
    # Direct flights
    direct_flights = {
        'Helsinki': ['Riga', 'Dublin', 'Tallinn'],
        'Riga': ['Helsinki', 'Tallinn', 'Vienna', 'Dublin'],
        'Vienna': ['Riga', 'Reykjavik', 'Dublin'],
        'Reykjavik': ['Vienna', 'Helsinki', 'Dublin'],
        'Tallinn': ['Riga', 'Dublin', 'Helsinki'],
        'Dublin': ['Riga', 'Helsinki', 'Tallinn', 'Vienna', 'Reykjavik']
    }
    
    # Constraints
    constraints = [
        {'city': 'Helsinki', 'day_range': (3, 5)},
        {'city': 'Vienna', 'day_range': (2, 3)},
        {'city': 'Tallinn', 'day_range': (7, 11)}
    ]
    
    # Generate all possible permutations of the cities
    for perm in permutations(cities.keys()):
        itinerary = []
        current_day = 1
        valid = True
        
        # Check if the permutation satisfies all constraints
        for city in perm:
            days_needed = cities[city]
            
            # Check if the current city can be placed within the constraints
            for constraint in constraints:
                if constraint['city'] == city:
                    start, end = constraint['day_range']
                    if not (current_day <= end and current_day + days_needed - 1 >= start):
                        valid = False
                        break
            if not valid:
                break
            
            # Add the city to the itinerary
            end_day = current_day + days_needed - 1
            itinerary.append({
                'day_range': f'Day {current_day}-{end_day}',
                'place': city
            })
            current_day = end_day + 1
            
            # Check if we've exceeded the total days
            if current_day > 15:
                valid = False
                break
            
            # Check if the next city is reachable via direct flight
            if perm.index(city) < len(perm) - 1:
                next_city = perm[perm.index(city) + 1]
                if next_city not in direct_flights[city]:
                    valid = False
                    break
                
                # Add flight to the itinerary
                itinerary.append({
                    'flying': f'Day {end_day}-{end_day}',
                    'from': city,
                    'to': next_city
                })
        
        if valid and current_day - 1 == 15:
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