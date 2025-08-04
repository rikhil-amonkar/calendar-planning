from z3 import *
import json

def solve_itinerary():
    # Cities and their required days
    cities = ['Helsinki', 'Warsaw', 'Madrid', 'Split', 'Reykjavik', 'Budapest']
    city_days = {
        'Helsinki': 2,
        'Warsaw': 3,
        'Madrid': 4,
        'Split': 4,
        'Reykjavik': 2,
        'Budapest': 4
    }
    city_to_idx = {city: idx for idx, city in enumerate(cities)}

    # Direct flights (bidirectional)
    direct_flights = [
        ('Helsinki', 'Reykjavik'),
        ('Budapest', 'Warsaw'),
        ('Madrid', 'Split'),
        ('Helsinki', 'Split'),
        ('Helsinki', 'Madrid'),
        ('Helsinki', 'Budapest'),
        ('Reykjavik', 'Warsaw'),
        ('Helsinki', 'Warsaw'),
        ('Madrid', 'Budapest'),
        ('Budapest', 'Reykjavik'),
        ('Madrid', 'Warsaw'),
        ('Warsaw', 'Split'),
        ('Reykjavik', 'Madrid')
    ]
    # Create flight pairs in both directions
    flight_pairs = set()
    for a, b in direct_flights:
        flight_pairs.add((city_to_idx[a], city_to_idx[b]))
        flight_pairs.add((city_to_idx[b], city_to_idx[a]))

    days_total = 14
    s = Solver()

    # Variables: city for each day (1-based)
    day_city = [Int(f'day_{i}') for i in range(1, days_total + 1)]
    for dc in day_city:
        s.add(dc >= 0, dc < len(cities))

    # Fixed constraints:
    # Helsinki on days 1 and 2
    s.add(day_city[0] == city_to_idx['Helsinki'])
    s.add(day_city[1] == city_to_idx['Helsinki'])

    # Warsaw on days 9, 10, 11
    s.add(day_city[8] == city_to_idx['Warsaw'])
    s.add(day_city[9] == city_to_idx['Warsaw'])
    s.add(day_city[10] == city_to_idx['Warsaw'])

    # Reykjavik on day 8
    s.add(day_city[7] == city_to_idx['Reykjavik'])

    # Flight transitions
    for i in range(days_total - 1):
        current = day_city[i]
        next_ = day_city[i + 1]
        s.add(Or(current == next_, (current, next_) in flight_pairs))

    # Total days per city accounting for flight days
    for city, required in city_days.items():
        c = city_to_idx[city]
        # Count days where city is current or next with flight
        total = Sum([If(day_city[i] == c, 1, 0) for i in range(days_total)]) + \
                Sum([If(And(i < days_total - 1, day_city[i] != c, day_city[i + 1] == c), 1, 0) 
                 for i in range(days_total - 1)])
        s.add(total == required)

    if s.check() == sat:
        m = s.model()
        itinerary = []
        for day in range(1, days_total + 1):
            city_idx = m.evaluate(day_city[day - 1]).as_long()
            itinerary.append({'day': day, 'place': cities[city_idx]})
        return json.dumps({'itinerary': itinerary}, indent=2)
    else:
        return json.dumps({'error': 'No valid itinerary found'}, indent=2)

print(solve_itinerary())