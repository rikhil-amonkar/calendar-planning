import json
from z3 import *

def solve_itinerary():
    # Cities and their required days
    cities = {
        'Paris': 5,
        'Florence': 3,
        'Vienna': 2,
        'Porto': 3,
        'Munich': 5,
        'Nice': 5,
        'Warsaw': 3
    }
    
    # Direct flights (undirected)
    flight_pairs = [
        ('Florence', 'Vienna'),
        ('Florence', 'Munich'),
        ('Florence', 'Paris'),
        ('Vienna', 'Munich'),
        ('Vienna', 'Porto'),
        ('Vienna', 'Warsaw'),
        ('Vienna', 'Paris'),
        ('Vienna', 'Nice'),
        ('Paris', 'Warsaw'),
        ('Paris', 'Porto'),
        ('Paris', 'Nice'),
        ('Paris', 'Munich'),
        ('Munich', 'Warsaw'),
        ('Munich', 'Nice'),
        ('Munich', 'Porto'),
        ('Porto', 'Nice'),
        ('Porto', 'Warsaw'),
        ('Warsaw', 'Nice')
    ]
    
    # Create flight connections dictionary
    direct_flights = {city: set() for city in cities}
    for a, b in flight_pairs:
        direct_flights[a].add(b)
        direct_flights[b].add(a)
    
    # Day variables: each day is assigned a city
    day_to_city = [Int(f'day_{i}') for i in range(1, 21)]
    
    # City encodings
    city_ids = {city: i for i, city in enumerate(cities)}
    id_to_city = {i: city for city, i in city_ids.items()}
    
    s = Solver()
    
    # Each day must be one of the cities
    for day_var in day_to_city:
        s.add(Or([day_var == city_ids[city] for city in cities]))
    
    # Flight transitions between consecutive days
    for i in range(19):
        current = day_to_city[i]
        next_day = day_to_city[i+1]
        # Either stay or fly to connected city
        same_city = current == next_day
        possible_flights = []
        for city_a, city_b in flight_pairs:
            possible_flights.append(And(current == city_ids[city_a], next_day == city_ids[city_b]))
            possible_flights.append(And(current == city_ids[city_b], next_day == city_ids[city_a]))
        s.add(Or(same_city, Or(possible_flights)))
    
    # Fixed stays
    # Porto days 1-3
    for i in range(3):
        s.add(day_to_city[i] == city_ids['Porto'])
    
    # Warsaw days 13-15 (indices 12-14)
    for i in range(12, 15):
        s.add(day_to_city[i] == city_ids['Warsaw'])
    
    # Vienna days 19-20 (indices 18-19)
    for i in range(18, 20):
        s.add(day_to_city[i] == city_ids['Vienna'])
    
    # Count days in each city
    for city, req_days in cities.items():
        count = Sum([If(day == city_ids[city], 1, 0) for day in day_to_city])
        s.add(count == req_days)
    
    # Check solution
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for i in range(20):
            day_num = i + 1
            city_id = model.evaluate(day_to_city[i]).as_long()
            city = id_to_city[city_id]
            itinerary.append({'day': day_num, 'city': city})
        
        # Verify all constraints
        day_counts = {city: 0 for city in cities}
        for entry in itinerary:
            day_counts[entry['city']] += 1
        
        for city, req in cities.items():
            assert day_counts[city] == req, f"{city} has {day_counts[city]} days, expected {req}"
        
        for i in range(19):
            current = itinerary[i]['city']
            next_c = itinerary[i+1]['city']
            if current != next_c:
                assert next_c in direct_flights[current], f"No flight from {current} to {next_c}"
        
        return {'itinerary': itinerary}
    else:
        return None

result = solve_itinerary()
if result:
    print(json.dumps(result, indent=2))
else:
    print("No solution found")