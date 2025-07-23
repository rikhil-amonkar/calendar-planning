import json
from itertools import permutations

def find_itinerary():
    cities = {
        'Dublin': {'duration': 3, 'constraints': [(7, 9)]},
        'Madrid': {'duration': 2, 'constraints': [(2, 3)]},
        'Oslo': {'duration': 3, 'constraints': []},
        'London': {'duration': 2, 'constraints': []},
        'Vilnius': {'duration': 3, 'constraints': []},
        'Berlin': {'duration': 5, 'constraints': [(3, 7)]}
    }

    direct_flights = {
        'London': ['Madrid', 'Oslo', 'Dublin', 'Berlin'],
        'Madrid': ['London', 'Oslo', 'Dublin', 'Berlin'],
        'Oslo': ['Vilnius', 'Madrid', 'London', 'Berlin', 'Dublin'],
        'Berlin': ['Vilnius', 'Madrid', 'Oslo', 'London', 'Dublin'],
        'Dublin': ['Madrid', 'Oslo', 'London', 'Berlin'],
        'Vilnius': ['Oslo', 'Berlin']
    }

    city_list = list(cities.keys())
    
    # Try all possible permutations of cities
    for perm in permutations(city_list):
        itinerary = []
        current_city = None
        day = 1
        visited = set()
        constraints_satisfied = {city: False for city in cities if cities[city]['constraints']}
        
        for city in perm:
            if current_city is None:
                # First city in itinerary
                current_city = city
                start_day = day
                end_day = start_day + cities[city]['duration'] - 1
                
                # Check if this exceeds 13 days
                if end_day > 13:
                    break
                    
                itinerary.append({
                    'day_range': f'Day {start_day}-{end_day}',
                    'place': city
                })
                visited.add(city)
                day = end_day + 1
                
                # Check constraints for this city
                if cities[city]['constraints']:
                    for (start, end) in cities[city]['constraints']:
                        if start_day <= start and end_day >= end:
                            constraints_satisfied[city] = True
            else:
                # Check if we can fly to this city
                if city not in direct_flights[current_city]:
                    break
                    
                # Add transition day (1 day for flight)
                flight_day = day
                day += 1
                
                # Check if we've exceeded 13 days
                if day > 13:
                    break
                    
                # Stay in the new city
                start_day = day
                end_day = start_day + cities[city]['duration'] - 1
                
                # Check if this exceeds 13 days
                if end_day > 13:
                    break
                    
                itinerary.append({
                    'day_range': f'Day {start_day}-{end_day}',
                    'place': city
                })
                visited.add(city)
                current_city = city
                day = end_day + 1
                
                # Check constraints for this city
                if cities[city]['constraints']:
                    for (start, end) in cities[city]['constraints']:
                        if start_day <= start and end_day >= end:
                            constraints_satisfied[city] = True
        
        # Check if all cities were visited and all constraints are satisfied
        if (len(visited) == len(city_list) and 
            all(value for value in constraints_satisfied.values()) and 
            day - 1 <= 13):
            return {'itinerary': itinerary}
    
    return {'itinerary': []}

result = find_itinerary()
print(json.dumps(result, indent=2))