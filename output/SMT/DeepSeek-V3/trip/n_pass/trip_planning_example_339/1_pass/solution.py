import json
from z3 import *

def solve_itinerary():
    # Cities encoding
    cities = {
        'Warsaw': 0,
        'Budapest': 1,
        'Paris': 2,
        'Riga': 3
    }
    inv_cities = {v: k for k, v in cities.items()}

    # Direct flights: adjacency list
    direct_flights = {
        0: [1, 2, 3],  # Warsaw -> Budapest, Paris, Riga
        1: [0, 2],     # Budapest -> Warsaw, Paris
        2: [0, 1, 3],   # Paris -> Warsaw, Budapest, Riga
        3: [0, 2]       # Riga -> Warsaw, Paris
    }

    # Create solver
    s = Solver()

    # Variables: day[i] is the city visited on day i+1 (days are 1-based)
    day = [Int(f'day_{i}') for i in range(17)]

    # Constraint: each day's city must be 0, 1, 2, or 3
    for d in day:
        s.add(Or([d == c for c in cities.values()]))

    # Constraint: days 1 and 2 are Warsaw (0)
    s.add(day[0] == cities['Warsaw'])
    s.add(day[1] == cities['Warsaw'])

    # Constraint: Riga must be visited between days 11-17 (inclusive)
    s.add(Or([day[i] == cities['Riga'] for i in range(10, 17)]))

    # Constraint: transitions between cities must be via direct flights
    for i in range(16):
        current_city = day[i]
        next_city = day[i + 1]
        s.add(Or(current_city == next_city, next_city in direct_flights[current_city]))

    # Count days per city
    def count_city(city_num):
        return Sum([If(day[i] == city_num, 1, 0) for i in range(17)])

    s.add(count_city(cities['Warsaw']) == 2)
    s.add(count_city(cities['Budapest']) == 7)
    s.add(count_city(cities['Paris']) == 4)
    s.add(count_city(cities['Riga']) == 7)

    # Check and get model
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for i in range(17):
            city_num = model.evaluate(day[i]).as_long()
            itinerary.append({'day': i + 1, 'place': inv_cities[city_num]})
        
        # Verify the counts
        counts = {city: 0 for city in cities}
        for entry in itinerary:
            counts[entry['place']] += 1
        
        # Check if counts meet the requirements
        assert counts['Warsaw'] == 2
        assert counts['Budapest'] == 7
        assert counts['Paris'] == 4
        assert counts['Riga'] == 7

        # Verify Riga is between days 11-17
        riga_days = [entry['day'] for entry in itinerary if entry['place'] == 'Riga']
        assert any(11 <= day <= 17 for day in riga_days)

        # Verify transitions are via direct flights
        for i in range(16):
            current_place = itinerary[i]['place']
            next_place = itinerary[i+1]['place']
            if current_place != next_place:
                assert cities[next_place] in direct_flights[cities[current_place]]

        return {'itinerary': itinerary}
    else:
        return None

result = solve_itinerary()
if result:
    print(json.dumps(result, indent=2))
else:
    print("No solution found")