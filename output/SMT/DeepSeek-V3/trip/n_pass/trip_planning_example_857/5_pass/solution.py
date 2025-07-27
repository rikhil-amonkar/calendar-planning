import json
from z3 import *

def solve_itinerary():
    # Cities with their required durations
    cities = {
        'Porto': 2,
        'Geneva': 3,
        'Mykonos': 3,
        'Manchester': 4,
        'Hamburg': 5,
        'Naples': 5,
        'Frankfurt': 2
    }
    city_list = list(cities.keys())
    city_map = {city: idx for idx, city in enumerate(city_list)}
    idx_to_city = {idx: city for city, idx in city_map.items()}

    # Direct flight connections (bidirectional)
    direct_flights = [
        ('Hamburg', 'Frankfurt'), ('Naples', 'Mykonos'), ('Hamburg', 'Porto'),
        ('Hamburg', 'Geneva'), ('Mykonos', 'Geneva'), ('Frankfurt', 'Geneva'),
        ('Frankfurt', 'Porto'), ('Geneva', 'Porto'), ('Geneva', 'Manchester'),
        ('Naples', 'Manchester'), ('Frankfurt', 'Naples'), ('Frankfurt', 'Manchester'),
        ('Naples', 'Geneva'), ('Porto', 'Manchester'), ('Hamburg', 'Manchester')
    ]
    
    # Create flight connections (both directions)
    flight_connections = set()
    for a, b in direct_flights:
        flight_connections.add((city_map[a], city_map[b]))
        flight_connections.add((city_map[b], city_map[a]))

    # Z3 solver setup
    s = Solver()
    num_days = 18
    day = [Int(f"day_{i}") for i in range(num_days)]

    # Each day must be a valid city index
    for d in day:
        s.add(And(d >= 0, d < len(city_list)))

    # Duration constraints
    for city, dur in cities.items():
        city_idx = city_map[city]
        s.add(Sum([If(day[i] == city_idx, 1, 0) for i in range(num_days)]) == dur)

    # Event constraints
    # Frankfurt show on days 5-6 (days 4-5 in 0-based)
    s.add(day[4] == city_map['Frankfurt'])
    s.add(day[5] == city_map['Frankfurt'])

    # Mykonos friend visit between days 10-12 (days 9-11 in 0-based)
    s.add(Or([day[i] == city_map['Mykonos'] for i in range(9, 12)]))

    # Manchester wedding between days 15-18 (days 14-17 in 0-based)
    s.add(Or([day[i] == city_map['Manchester'] for i in range(14, 18)]))

    # Flight constraints between consecutive days
    for i in range(num_days - 1):
        current = day[i]
        next_day = day[i+1]
        s.add(Or(
            current == next_day,  # Stay in same city
            Or([And(current == a, next_day == b) for a, b in flight_connections])  # Direct flight
        ))

    # Additional constraints to help the solver
    # Ensure we don't have too many city changes
    s.add(Sum([If(day[i] != day[i+1], 1, 0) for i in range(num_days - 1)]) <= 6)

    # Solve
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for i in range(num_days):
            city_idx = m.evaluate(day[i]).as_long()
            itinerary.append({"day": i+1, "place": idx_to_city[city_idx]})

        # Verify all constraints
        city_counts = {city: 0 for city in city_list}
        for entry in itinerary:
            city_counts[entry['place']] += 1

        for city, dur in cities.items():
            assert city_counts[city] == dur, f"Duration mismatch for {city}"

        # Verify flight connections
        for i in range(num_days - 1):
            current = itinerary[i]['place']
            next_c = itinerary[i+1]['place']
            if current != next_c:
                assert (city_map[current], city_map[next_c]) in flight_connections, \
                    f"No flight from {current} to {next_c} on day {i+1}"

        # Verify events
        assert itinerary[4]['place'] == 'Frankfurt' and itinerary[5]['place'] == 'Frankfurt'
        assert any(10 <= entry['day'] <= 12 for entry in itinerary if entry['place'] == 'Mykonos')
        assert any(15 <= entry['day'] <= 18 for entry in itinerary if entry['place'] == 'Manchester')

        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

result = solve_itinerary()
print(json.dumps(result, indent=2))