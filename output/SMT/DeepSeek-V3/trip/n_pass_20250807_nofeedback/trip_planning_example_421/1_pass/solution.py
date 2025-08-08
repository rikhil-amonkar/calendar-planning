from z3 import *

def solve_itinerary():
    # Cities
    Nice, Dublin, Frankfurt, Krakow, Lyon = Ints('Nice Dublin Frankfurt Krakow Lyon')
    cities = {
        'Nice': Nice,
        'Dublin': Dublin,
        'Frankfurt': Frankfurt,
        'Krakow': Krakow,
        'Lyon': Lyon
    }
    city_list = ['Nice', 'Dublin', 'Frankfurt', 'Krakow', 'Lyon']
    city_to_num = {city: idx for idx, city in enumerate(city_list)}
    num_to_city = {idx: city for city, idx in city_to_num.items()}

    # Direct flights
    direct_flights = {
        ('Nice', 'Dublin'),
        ('Dublin', 'Frankfurt'),
        ('Dublin', 'Krakow'),
        ('Krakow', 'Frankfurt'),
        ('Lyon', 'Frankfurt'),
        ('Nice', 'Frankfurt'),
        ('Lyon', 'Dublin'),
        ('Nice', 'Lyon')
    }
    # Make it bidirectional
    bidirectional = set()
    for a, b in direct_flights:
        bidirectional.add((a, b))
        bidirectional.add((b, a))
    direct_flights = bidirectional

    # Days
    days = 20
    day_vars = [Int(f'day_{i}') for i in range(1, days + 1)]

    s = Solver()

    # Each day variable must be one of the city numbers
    for day in day_vars:
        s.add(Or([day == city_to_num[city] for city in city_list]))

    # City day counts
    s.add(Sum([If(day == city_to_num['Nice'], 1, 0) for day in day_vars]) == 5)
    s.add(Sum([If(day == city_to_num['Krakow'], 1, 0) for day in day_vars]) == 6)
    s.add(Sum([If(day == city_to_num['Dublin'], 1, 0) for day in day_vars]) == 7)
    s.add(Sum([If(day == city_to_num['Lyon'], 1, 0) for day in day_vars]) == 4)
    s.add(Sum([If(day == city_to_num['Frankfurt'], 1, 0) for day in day_vars]) == 2)

    # Nice between day 1-5 (inclusive)
    for i in range(1, 6):
        s.add(day_vars[i-1] == city_to_num['Nice'])

    # Frankfurt on days 19 and 20
    s.add(day_vars[18] == city_to_num['Frankfurt'])  # day 19
    s.add(day_vars[19] == city_to_num['Frankfurt'])  # day 20

    # Flight constraints: consecutive days must be same city or have a direct flight
    for i in range(days - 1):
        current_city = day_vars[i]
        next_city = day_vars[i+1]
        s.add(Or(
            current_city == next_city,
            *[
                And(current_city == city_to_num[a], next_city == city_to_num[b])
                for (a, b) in direct_flights
            ]
        ))

    if s.check() == sat:
        model = s.model()
        itinerary = []
        for i in range(days):
            day_num = i + 1
            city_num = model.evaluate(day_vars[i]).as_long()
            city = num_to_city[city_num]
            itinerary.append({'day': day_num, 'place': city})
        return {'itinerary': itinerary}
    else:
        return None

result = solve_itinerary()
import json
print(json.dumps(result, indent=2))