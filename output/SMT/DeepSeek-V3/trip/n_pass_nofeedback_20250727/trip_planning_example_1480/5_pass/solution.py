from z3 import *
import json

def solve_itinerary():
    # Cities and their required days
    cities = {
        'Istanbul': 4,
        'Vienna': 4,
        'Riga': 2,
        'Brussels': 2,
        'Madrid': 4,
        'Vilnius': 4,
        'Venice': 5,
        'Geneva': 4,
        'Munich': 5,
        'Reykjavik': 2
    }
    
    # Direct flights (bidirectional)
    direct_flights = [
        ('Munich', 'Vienna'),
        ('Istanbul', 'Brussels'),
        ('Vienna', 'Vilnius'),
        ('Madrid', 'Munich'),
        ('Venice', 'Brussels'),
        ('Riga', 'Brussels'),
        ('Geneva', 'Istanbul'),
        ('Munich', 'Reykjavik'),
        ('Vienna', 'Istanbul'),
        ('Riga', 'Istanbul'),
        ('Reykjavik', 'Vienna'),
        ('Venice', 'Munich'),
        ('Madrid', 'Venice'),
        ('Vilnius', 'Istanbul'),
        ('Venice', 'Vienna'),
        ('Venice', 'Istanbul'),
        ('Reykjavik', 'Madrid'),
        ('Riga', 'Munich'),
        ('Munich', 'Istanbul'),
        ('Reykjavik', 'Brussels'),
        ('Vilnius', 'Brussels'),
        ('Vilnius', 'Munich'),
        ('Madrid', 'Vienna'),
        ('Vienna', 'Riga'),
        ('Geneva', 'Vienna'),
        ('Geneva', 'Brussels'),
        ('Geneva', 'Madrid'),
        ('Geneva', 'Munich'),
        ('Madrid', 'Brussels'),
        ('Vienna', 'Brussels'),
        ('Madrid', 'Istanbul'),
        ('Riga', 'Vilnius')
    ]
    
    # Create bidirectional flight connections
    flight_connections = set()
    for a, b in direct_flights:
        flight_connections.add((a, b))
        flight_connections.add((b, a))
    
    # Create Z3 variables for each day
    days = 27
    day_vars = [Int(f'day_{i}') for i in range(1, days + 1)]
    
    # City to integer mapping
    city_ids = {city: idx for idx, city in enumerate(cities.keys())}
    id_to_city = {idx: city for city, idx in city_ids.items()}
    
    s = Solver()
    
    # Each day must be assigned to a valid city
    for day in day_vars:
        s.add(Or([day == city_ids[city] for city in cities]))
    
    # Total days per city must match requirements
    for city, total_days in cities.items():
        city_id = city_ids[city]
        s.add(Sum([If(day == city_id, 1, 0) for day in day_vars]) == total_days)
    
    # Fixed constraints:
    # Geneva days 1-4
    for i in range(1, 5):
        s.add(day_vars[i-1] == city_ids['Geneva'])
    
    # Venice days 7-11 (workshop)
    for i in range(7, 12):
        s.add(day_vars[i-1] == city_ids['Venice'])
    
    # Vilnius days 20-23 (friends)
    for i in range(20, 24):
        s.add(day_vars[i-1] == city_ids['Vilnius'])
    
    # Brussels days 26-27 (wedding)
    s.add(day_vars[25] == city_ids['Brussels'])
    s.add(day_vars[26] == city_ids['Brussels'])
    
    # Flight connectivity constraints
    for i in range(days - 1):
        current = day_vars[i]
        next_day = day_vars[i + 1]
        
        # Either stay in same city or take a direct flight
        same_city = current == next_day
        flight_options = []
        for (a, b) in flight_connections:
            flight_options.append(And(current == city_ids[a], next_day == city_ids[b]))
        s.add(Or(same_city, *flight_options))
    
    # Try to find a solution
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for i in range(1, days + 1):
            city_id = model[day_vars[i-1]].as_long()
            itinerary.append({'day': i, 'place': id_to_city[city_id]})
        
        # Verify all constraints are satisfied
        city_counts = {city: 0 for city in cities}
        for entry in itinerary:
            city_counts[entry['place']] += 1
        
        for city, count in city_counts.items():
            assert count == cities[city], f"City {city} has incorrect day count"
        
        # Verify flight connections
        for i in range(days - 1):
            current = itinerary[i]['place']
            next_city = itinerary[i+1]['place']
            if current != next_city:
                assert (current, next_city) in flight_connections, \
                    f"No flight from {current} to {next_city} on day {i+1}"
        
        return json.dumps({'itinerary': itinerary}, indent=2)
    else:
        return json.dumps({'error': 'No valid itinerary found'}, indent=2)

print(solve_itinerary())