import json
from itertools import permutations

def find_itinerary():
    # Define cities and their required days
    cities = {
        'Copenhagen': 5,
        'Geneva': 3,
        'Mykonos': 2,
        'Naples': 4,
        'Prague': 2,
        'Dubrovnik': 3,
        'Athens': 4,
        'Santorini': 5,
        'Brussels': 4,
        'Munich': 5
    }
    
    # Define constraints (city, start_day, end_day)
    constraints = {
        'Copenhagen': (11, 15),
        'Mykonos': (27, 28),
        'Naples': (5, 8),
        'Athens': (8, 11)
    }
    
    # Define direct flights
    direct_flights = {
        'Copenhagen': ['Dubrovnik', 'Brussels', 'Naples', 'Prague', 'Athens', 'Geneva', 'Munich', 'Santorini'],
        'Geneva': ['Prague', 'Athens', 'Mykonos', 'Naples', 'Santorini', 'Dubrovnik', 'Brussels', 'Munich'],
        'Mykonos': ['Geneva', 'Naples', 'Athens', 'Munich'],
        'Naples': ['Dubrovnik', 'Mykonos', 'Copenhagen', 'Athens', 'Munich', 'Santorini', 'Geneva', 'Brussels'],
        'Prague': ['Geneva', 'Athens', 'Brussels', 'Copenhagen', 'Munich'],
        'Dubrovnik': ['Copenhagen', 'Naples', 'Athens', 'Munich', 'Geneva'],
        'Athens': ['Geneva', 'Dubrovnik', 'Naples', 'Prague', 'Mykonos', 'Santorini', 'Brussels', 'Munich', 'Copenhagen'],
        'Santorini': ['Geneva', 'Athens', 'Naples', 'Copenhagen'],
        'Brussels': ['Copenhagen', 'Naples', 'Prague', 'Athens', 'Munich', 'Geneva'],
        'Munich': ['Mykonos', 'Naples', 'Dubrovnik', 'Brussels', 'Athens', 'Geneva', 'Copenhagen', 'Prague']
    }
    
    # Fix any typos in city names
    direct_flights['Athens'] = ['Geneva', 'Dubrovnik', 'Naples', 'Prague', 'Mykonos', 'Santorini', 'Brussels', 'Munich', 'Copenhagen']
    direct_flights['Brussels'] = ['Copenhagen', 'Naples', 'Prague', 'Athens', 'Munich', 'Geneva']
    direct_flights['Munich'] = ['Mykonos', 'Naples', 'Dubrovnik', 'Brussels', 'Athens', 'Geneva', 'Copenhagen', 'Prague']
    
    def is_valid_placement(city, start_day, end_day):
        # Check if placement fits within 28 days
        if end_day > 28:
            return False
            
        # Check constraints if they exist
        if city in constraints:
            c_start, c_end = constraints[city]
            if not (start_day <= c_end and end_day >= c_start):
                return False
        return True
    
    def backtrack(current_itinerary, remaining_cities, current_day, last_city):
        if current_day > 29:  # We want to end exactly at day 28 (current_day would be 29 after)
            return None
            
        if current_day == 29 and not remaining_cities:
            return current_itinerary
            
        if not remaining_cities:
            return None
            
        # Try cities with constraints first if they need to be placed now
        for city in remaining_cities:
            # Check if this city has constraints that need to be placed now
            if city in constraints:
                c_start, c_end = constraints[city]
                if current_day > c_end:
                    continue  # Can't place this constrained city anymore
                if current_day + cities[city] - 1 < c_start:
                    continue  # Not time to place this constrained city yet
            
            # Check flight connection
            if last_city and city not in direct_flights.get(last_city, []):
                continue
                
            days = cities[city]
            start_day = current_day
            end_day = current_day + days - 1
            
            if not is_valid_placement(city, start_day, end_day):
                continue
                
            new_itinerary = current_itinerary + [{
                'day_range': f'Day {start_day}-{end_day}',
                'place': city
            }]
            
            result = backtrack(
                new_itinerary,
                [c for c in remaining_cities if c != city],
                end_day + 1,
                city
            )
            
            if result:
                return result
                
        return None
    
    # Start with all cities
    all_cities = list(cities.keys())
    
    # Try different orderings to find a valid itinerary
    for perm in permutations(all_cities):
        result = backtrack([], list(perm), 1, None)
        if result:
            # Verify we've used exactly 28 days
            last_day = int(result[-1]['day_range'].split('-')[1].replace('Day ', ''))
            if last_day == 28:
                return {'itinerary': result}
    
    return {'itinerary': []}

# Execute the function and print the result
result = find_itinerary()
print(json.dumps(result))