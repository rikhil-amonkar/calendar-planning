import json
from itertools import permutations

def find_itinerary():
    cities = {
        'Oslo': 2,
        'Helsinki': 2,
        'Edinburgh': 3,
        'Riga': 2,
        'Tallinn': 5,
        'Budapest': 5,
        'Vilnius': 5,
        'Porto': 5,
        'Geneva': 4
    }
    
    flight_routes = {
        'Porto': ['Oslo', 'Edinburgh', 'Geneva'],
        'Edinburgh': ['Budapest', 'Geneva', 'Porto', 'Oslo', 'Helsinki', 'Riga'],
        'Riga': ['Tallinn', 'Oslo', 'Helsinki', 'Vilnius'],
        'Tallinn': ['Vilnius', 'Helsinki', 'Oslo'],
        'Vilnius': ['Helsinki', 'Oslo'],
        'Helsinki': ['Budapest', 'Oslo', 'Geneva'],
        'Budapest': ['Geneva', 'Oslo'],
        'Geneva': ['Oslo', 'Porto'],
        'Oslo': ['Porto', 'Edinburgh', 'Geneva', 'Riga', 'Tallinn', 'Vilnius', 'Budapest', 'Helsinki']
    }
    
    # Constraints
    wedding_in_tallinn = (4, 8)  # Must be in Tallinn between day 4 and day 8
    meet_in_oslo = (24, 25)      # Must be in Oslo between day 24 and day 25
    
    # Generate all possible permutations of the cities
    city_names = list(cities.keys())
    
    # We'll try all possible permutations, but in reality this is computationally expensive for 9 cities
    # For the sake of this problem, we'll proceed with this approach
    for perm in permutations(city_names):
        itinerary = []
        current_day = 1
        valid = True
        
        # Check if Tallinn is visited within the wedding days
        tallinn_visited = False
        tallinn_days = []
        oslo_visited = False
        oslo_days = []
        
        prev_city = None
        for city in perm:
            if prev_city is not None:
                if city not in flight_routes[prev_city]:
                    valid = False
                    break
            
            duration = cities[city]
            day_start = current_day
            day_end = current_day + duration - 1
            itinerary.append({'day_range': f'Day {day_start}-{day_end}', 'place': city})
            
            if city == 'Tallinn':
                tallinn_visited = True
                tallinn_days = (day_start, day_end)
            if city == 'Oslo':
                oslo_visited = True
                oslo_days = (day_start, day_end)
            
            current_day = day_end + 1
            prev_city = city
        
        if not valid:
            continue
        
        # Check if the total days are 25
        if current_day - 1 != 25:
            continue
        
        # Check wedding constraint
        if not tallinn_visited:
            valid = False
            continue
        if not (tallinn_days[0] <= wedding_in_tallinn[1] and tallinn_days[1] >= wedding_in_tallinn[0]):
            valid = False
            continue
        
        # Check Oslo meeting constraint
        if not oslo_visited:
            valid = False
            continue
        if not (oslo_days[0] <= meet_in_oslo[1] and oslo_days[1] >= meet_in_oslo[0]):
            valid = False
            continue
        
        if valid:
            return {'itinerary': itinerary}
    
    return {'itinerary': []}

result = find_itinerary()
print(json.dumps(result, indent=2))