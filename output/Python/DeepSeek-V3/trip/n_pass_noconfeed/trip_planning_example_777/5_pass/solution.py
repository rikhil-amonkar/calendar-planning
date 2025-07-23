import json
from itertools import permutations

def find_itinerary():
    # Cities and required days
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
        'Helsinki': ['Riga', 'Dublin', 'Tallinn', 'Reykjavik'],
        'Riga': ['Helsinki', 'Tallinn', 'Vienna', 'Dublin'],
        'Vienna': ['Riga', 'Dublin', 'Reykjavik'],
        'Reykjavik': ['Vienna', 'Helsinki', 'Dublin'],
        'Tallinn': ['Dublin', 'Helsinki', 'Riga'],
        'Dublin': ['Helsinki', 'Riga', 'Tallinn', 'Vienna', 'Reykjavik']
    }
    
    # Constraints
    constraints = {
        'Helsinki': (3, 5),  # Helsinki between day 3-5 (3 days means days 3-5)
        'Vienna': (2, 3),    # Vienna between day 2-3 (2 days means days 2-3)
        'Tallinn': (7, 11)   # Tallinn between day 7-11 (5 days means days 7-11)
    }
    
    total_days = 15
    
    # We'll try different starting points and build the itinerary step by step
    # Let's try starting with Vienna since it has the earliest constraint
    for start_city in ['Vienna', 'Helsinki', 'Riga', 'Reykjavik', 'Tallinn', 'Dublin']:
        itinerary = []
        visited = set()
        current_day = 1
        
        # First place must be Vienna or Helsinki or something else?
        # Let's try to place constrained cities first
        
        # Try to place Vienna first (days 2-3)
        if start_city == 'Vienna':
            if current_day != 1:
                continue  # Vienna must start on day 1 to fit in days 2-3
            itinerary.append({
                'city': 'Vienna',
                'start_day': 2,
                'end_day': 3
            })
            visited.add('Vienna')
            current_day = 4
        
        # Then try to place Helsinki (days 3-5)
        if 'Helsinki' not in visited and current_day <= 3:
            itinerary.append({
                'city': 'Helsinki',
                'start_day': 3,
                'end_day': 5
            })
            visited.add('Helsinki')
            current_day = 6
        
        # Then try to place Tallinn (days 7-11)
        if 'Tallinn' not in visited and current_day <= 7:
            itinerary.append({
                'city': 'Tallinn',
                'start_day': 7,
                'end_day': 11
            })
            visited.add('Tallinn')
            current_day = 12
        
        # Now fill in the remaining cities
        remaining_cities = [c for c in cities if c not in visited]
        for city in remaining_cities:
            if current_day + cities[city] - 1 > total_days:
                continue  # Doesn't fit
            
            # Check flight connection from previous city
            if itinerary and city not in direct_flights[itinerary[-1]['city']]:
                continue
            
            itinerary.append({
                'city': city,
                'start_day': current_day,
                'end_day': current_day + cities[city] - 1
            })
            current_day += cities[city]
            visited.add(city)
        
        # Check if all cities are visited and exactly 15 days used
        if len(visited) == len(cities) and current_day - 1 == total_days:
            # Format the itinerary
            formatted_itinerary = []
            for entry in sorted(itinerary, key=lambda x: x['start_day']):
                if entry['start_day'] == entry['end_day']:
                    day_range = f"Day {entry['start_day']}"
                else:
                    day_range = f"Day {entry['start_day']}-{entry['end_day']}"
                formatted_itinerary.append({
                    "day_range": day_range,
                    "place": entry['city']
                })
            return {"itinerary": formatted_itinerary}
    
    return {"itinerary": []}

# Execute and print the result
result = find_itinerary()
print(json.dumps(result, indent=2))