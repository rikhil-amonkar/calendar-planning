import json
from itertools import permutations

def find_itinerary():
    cities = {
        'Dublin': 5,
        'Helsinki': 3,
        'Riga': 3,
        'Reykjavik': 2,
        'Vienna': 2,
        'Tallinn': 5
    }
    
    constraints = {
        'Helsinki': {'meet_friends': (3, 5)},
        'Vienna': {'annual_show': (2, 3)},
        'Tallinn': {'wedding': (7, 11)}
    }
    
    direct_flights = {
        'Helsinki': ['Riga', 'Dublin', 'Tallinn', 'Reykjavik'],
        'Riga': ['Helsinki', 'Tallinn', 'Vienna', 'Dublin'],
        'Vienna': ['Riga', 'Dublin', 'Reykjavik'],
        'Reykjavik': ['Vienna', 'Helsinki', 'Dublin'],
        'Tallinn': ['Dublin', 'Helsinki', 'Riga'],
        'Dublin': ['Riga', 'Vienna', 'Reykjavik', 'Tallinn', 'Helsinki']
    }
    
    city_list = list(cities.keys())
    
    for perm in permutations(city_list):
        itinerary = []
        current_city = None
        remaining_days = cities.copy()
        day = 1
        valid = True
        
        for city in perm:
            if current_city is None:
                current_city = city
            else:
                if city not in direct_flights[current_city]:
                    valid = False
                    break
                current_city = city
            
            days_spent = 0
            max_days = remaining_days[city]
            
            if city == 'Helsinki':
                meet_start, meet_end = constraints['Helsinki']['meet_friends']
                if not (meet_start <= day <= meet_end):
                    valid = False
                    break
                days_spent = min(meet_end - day + 1, max_days)
            elif city == 'Vienna':
                show_start, show_end = constraints['Vienna']['annual_show']
                if day > show_end or day + max_days - 1 < show_start:
                    valid = False
                    break
                days_spent = max_days
            elif city == 'Tallinn':
                wedding_start, wedding_end = constraints['Tallinn']['wedding']
                if day > wedding_end or day + max_days - 1 < wedding_start:
                    valid = False
                    break
                days_spent = max_days
            else:
                days_spent = max_days
            
            itinerary.append({
                'day_range': f"Day {day}-{day + days_spent - 1}",
                'place': city
            })
            day += days_spent
            remaining_days[city] -= days_spent
            
            if day > 15:
                valid = False
                break
        
        if valid and all(v == 0 for v in remaining_days.values()):
            return {'itinerary': itinerary}
    
    return {'itinerary': []}

result = find_itinerary()
print(json.dumps(result, indent=2))