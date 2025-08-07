from z3 import *

def solve_itinerary():
    cities = ['Stuttgart', 'Istanbul', 'Vilnius', 'Seville', 'Geneva', 'Valencia', 'Munich', 'Reykjavik']
    
    direct_flights = {
        'Geneva': ['Istanbul', 'Munich', 'Valencia'],
        'Istanbul': ['Geneva', 'Stuttgart', 'Valencia', 'Vilnius', 'Munich'],
        'Reykjavik': ['Munich', 'Stuttgart'],
        'Stuttgart': ['Valencia', 'Istanbul', 'Reykjavik'],
        'Munich': ['Reykjavik', 'Geneva', 'Vilnius', 'Seville', 'Istanbul'],
        'Valencia': ['Stuttgart', 'Seville', 'Istanbul', 'Geneva', 'Munich'],
        'Seville': ['Valencia', 'Munich'],
        'Vilnius': ['Istanbul', 'Munich']
    }
    
    s = Solver()
    
    days = [Int(f'day_{i}') for i in range(1, 26)]
    
    for day in days:
        s.add(day >= 0, day < len(cities))
    
    # Reykjavik: days 1-3
    s.add(days[0] == cities.index('Reykjavik'))
    s.add(days[1] == cities.index('Reykjavik'))
    s.add(days[2] == cities.index('Reykjavik'))
    
    # Stuttgart: day 4 and 7
    s.add(days[3] == cities.index('Stuttgart'))
    s.add(days[6] == cities.index('Stuttgart'))
    
    # Munich: days 13-15
    s.add(days[12] == cities.index('Munich'))
    s.add(days[13] == cities.index('Munich'))
    s.add(days[14] == cities.index('Munich'))
    
    # Istanbul: days 19-22
    s.add(days[18] == cities.index('Istanbul'))
    s.add(days[19] == cities.index('Istanbul'))
    s.add(days[20] == cities.index('Istanbul'))
    s.add(days[21] == cities.index('Istanbul'))
    
    # Duration constraints
    # Stuttgart: 4 days (days 4 and 7 plus 2 more)
    s.add(Sum([If(days[i] == cities.index('Stuttgart'), 1, 0) for i in range(25)]) == 4)
    
    # Istanbul: 4 days (days 19-22)
    s.add(Sum([If(days[i] == cities.index('Istanbul'), 1, 0) for i in range(25)]) == 4)
    
    # Vilnius: 4 days
    s.add(Sum([If(days[i] == cities.index('Vilnius'), 1, 0) for i in range(25)]) == 4)
    
    # Seville: 3 days
    s.add(Sum([If(days[i] == cities.index('Seville'), 1, 0) for i in range(25)]) == 3)
    
    # Geneva: 5 days
    s.add(Sum([If(days[i] == cities.index('Geneva'), 1, 0) for i in range(25)]) == 5)
    
    # Valencia: 5 days
    s.add(Sum([If(days[i] == cities.index('Valencia'), 1, 0) for i in range(25)]) == 5)
    
    # Munich: 3 days (days 13-15)
    s.add(Sum([If(days[i] == cities.index('Munich'), 1, 0) for i in range(25)]) == 3)
    
    # Reykjavik: 4 days (days 1-3 plus 1 more)
    s.add(Sum([If(days[i] == cities.index('Reykjavik'), 1, 0) for i in range(25)]) == 4)
    
    # Flight constraints: consecutive days must be connected by direct flights or same city
    for i in range(24):
        current_city = days[i]
        next_city = days[i+1]
        current_city_name = cities[current_city.as_long()] if is_expr(current_city) else cities[current_city]
        next_city_name = cities[next_city.as_long()] if is_expr(next_city) else cities[next_city]
        s.add(Or(
            next_city == current_city,
            *[next_city == cities.index(neighbor) for neighbor in direct_flights[current_city_name]]
        ))
    
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for i in range(1, 26):
            day_var = days[i-1]
            city_index = model[day_var].as_long()
            itinerary.append({'day': i, 'city': cities[city_index]})
        
        # Verify counts
        counts = {city: 0 for city in cities}
        for entry in itinerary:
            counts[entry['city']] += 1
        
        expected_counts = {
            'Stuttgart': 4,
            'Istanbul': 4,
            'Vilnius': 4,
            'Seville': 3,
            'Geneva': 5,
            'Valencia': 5,
            'Munich': 3,
            'Reykjavik': 4
        }
        
        for city in counts:
            assert counts[city] == expected_counts[city], f"City {city} has {counts[city]} days, expected {expected_counts[city]}"
        
        return {'itinerary': itinerary}
    else:
        return {'error': 'No valid itinerary found'}

result = solve_itinerary()
import json
print(json.dumps(result, indent=2))