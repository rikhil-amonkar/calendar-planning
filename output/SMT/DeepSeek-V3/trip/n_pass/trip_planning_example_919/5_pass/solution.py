from z3 import *

def solve_itinerary():
    # Cities
    cities = ['Vienna', 'Milan', 'Rome', 'Riga', 'Lisbon', 'Vilnius', 'Oslo']
    city_to_int = {city: idx for idx, city in enumerate(cities)}
    int_to_city = {idx: city for idx, city in enumerate(cities)}
    
    # Direct flights (bidirectional)
    direct_flights = [
        ('Riga', 'Oslo'), ('Rome', 'Oslo'), ('Vienna', 'Milan'), ('Vienna', 'Vilnius'),
        ('Vienna', 'Lisbon'), ('Riga', 'Milan'), ('Lisbon', 'Oslo'), ('Rome', 'Riga'),
        ('Rome', 'Lisbon'), ('Vienna', 'Riga'), ('Vienna', 'Rome'), ('Milan', 'Oslo'),
        ('Vienna', 'Oslo'), ('Vilnius', 'Oslo'), ('Riga', 'Vilnius'), ('Vilnius', 'Milan'),
        ('Riga', 'Lisbon'), ('Milan', 'Lisbon')
    ]
    # Create flight pairs (including staying in same city)
    flight_pairs = set()
    for a, b in direct_flights:
        flight_pairs.add((city_to_int[a], city_to_int[b]))
        flight_pairs.add((city_to_int[b], city_to_int[a]))
    for city in cities:
        flight_pairs.add((city_to_int[city], city_to_int[city]))
    
    # Create solver
    s = Solver()
    
    # Variables: day 1 to 15
    days = [Int(f'day_{i}') for i in range(1, 16)]
    
    # Each day must be a valid city
    for day in days:
        s.add(day >= 0, day < len(cities))
    
    # Fixed constraints
    s.add(days[0] == city_to_int['Vienna'])  # Day 1 in Vienna
    s.add(days[3] == city_to_int['Vienna'])  # Day 4 in Vienna
    
    # Lisbon between day 11-13 (at least 1 day)
    s.add(Or(days[10] == city_to_int['Lisbon'],  # Day 11
             days[11] == city_to_int['Lisbon'],  # Day 12
             days[12] == city_to_int['Lisbon'])) # Day 13
    
    # Oslo between day 13-15 (at least 1 day)
    s.add(Or(days[12] == city_to_int['Oslo'],   # Day 13
             days[13] == city_to_int['Oslo'],   # Day 14
             days[14] == city_to_int['Oslo']))  # Day 15
    
    # Flight constraints between consecutive days
    for i in range(14):
        s.add(Or([And(days[i] == a, days[i+1] == b) for (a, b) in flight_pairs]))
    
    # Duration constraints
    duration = {
        'Vienna': 4,
        'Milan': 2,
        'Rome': 3,
        'Riga': 2,
        'Lisbon': 3,
        'Vilnius': 4,
        'Oslo': 3
    }
    for city, count in duration.items():
        s.add(Sum([If(d == city_to_int[city], 1, 0) for d in days]) == count)
    
    # Solve
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for i in range(15):
            day_num = i + 1
            city_idx = model.evaluate(days[i]).as_long()
            city = int_to_city[city_idx]
            itinerary.append({'day': day_num, 'place': city})
        
        # Verify counts
        counts = {city: 0 for city in cities}
        for entry in itinerary:
            counts[entry['place']] += 1
        for city, count in duration.items():
            assert counts[city] == count, f"{city} count mismatch"
        
        # Verify fixed days
        assert itinerary[0]['place'] == 'Vienna'
        assert itinerary[3]['place'] == 'Vienna'
        
        # Verify Lisbon and Oslo constraints
        lisbon_days = [e['day'] for e in itinerary if e['place'] == 'Lisbon']
        oslo_days = [e['day'] for e in itinerary if e['place'] == 'Oslo']
        assert any(11 <= d <= 13 for d in lisbon_days)
        assert any(13 <= d <= 15 for d in oslo_days)
        
        # Verify flights
        for i in range(14):
            current = itinerary[i]['place']
            next_c = itinerary[i+1]['place']
            assert (current == next_c) or ((city_to_int[current], city_to_int[next_c]) in flight_pairs)
        
        return {'itinerary': itinerary}
    else:
        return {"error": "No valid itinerary found"}

result = solve_itinerary()
import json
print(json.dumps(result, indent=2))