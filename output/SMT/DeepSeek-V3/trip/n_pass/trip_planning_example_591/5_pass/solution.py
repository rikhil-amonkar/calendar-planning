from z3 import *

def solve_itinerary():
    # Cities with their required days
    cities = {
        'Geneva': 4,
        'Munich': 7,
        'Valencia': 6,
        'Bucharest': 2,
        'Stuttgart': 2
    }
    city_list = list(cities.keys())
    city_map = {c: i for i, c in enumerate(city_list)}

    # Allowed direct flights (bidirectional)
    allowed_flights = [
        ('Geneva', 'Munich'),
        ('Munich', 'Valencia'),
        ('Bucharest', 'Valencia'),
        ('Munich', 'Bucharest'),
        ('Valencia', 'Stuttgart'),
        ('Geneva', 'Valencia')
    ]
    flight_map = set()
    for a, b in allowed_flights:
        flight_map.add((city_map[a], city_map[b]))
        flight_map.add((city_map[b], city_map[a]))

    # Days: 1..17
    days = 17
    s = Solver()

    # Decision variables: city for each day
    day_city = [Int(f'day_{i}') for i in range(days)]
    for dc in day_city:
        s.add(dc >= 0, dc < len(city_list))

    # Count days in each city
    counts = [0] * len(city_list)
    for i in range(days):
        for c in range(len(city_list)):
            counts[c] += If(day_city[i] == c, 1, 0)
    
    # Add constraints for required days
    for city, req_days in cities.items():
        s.add(counts[city_map[city]] == req_days)

    # Geneva must be days 1-4
    for i in range(4):
        s.add(day_city[i] == city_map['Geneva'])

    # Munich must include at least one day between 4-10
    munich_days = []
    for i in range(3, 10):  # days 4-10 (0-based)
        munich_days.append(day_city[i] == city_map['Munich'])
    s.add(Or(*munich_days))

    # Flight transitions must be allowed
    for i in range(days - 1):
        current = day_city[i]
        next_c = day_city[i + 1]
        s.add(Or(
            current == next_c,  # stay in same city
            And(current != next_c, 
                Or(*[And(current == a, next_c == b) for a, b in flight_map]))
        ))

    # Check for solution
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for i in range(days):
            city_idx = m.evaluate(day_city[i]).as_long()
            itinerary.append({'day': i + 1, 'place': city_list[city_idx]})
        
        # Verify counts
        counts_actual = {city: 0 for city in city_list}
        for entry in itinerary:
            counts_actual[entry['place']] += 1
        
        # Verify transitions
        valid = True
        for i in range(days - 1):
            current = itinerary[i]['place']
            next_p = itinerary[i + 1]['place']
            if current != next_p and (city_map[current], city_map[next_p]) not in flight_map:
                valid = False
                break
        
        if valid and all(counts_actual[city] == cities[city] for city in cities):
            return {'itinerary': itinerary}
    
    print("No valid itinerary found")
    return None

result = solve_itinerary()
if result:
    import json
    print(json.dumps(result, indent=2))