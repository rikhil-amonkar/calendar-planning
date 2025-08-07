import json
from z3 import *

def solve_itinerary():
    # Cities with their required days
    cities = {
        'Vienna': 4,
        'Barcelona': 2,
        'Edinburgh': 4,
        'Krakow': 3,
        'Riga': 4,
        'Hamburg': 2,
        'Paris': 2,
        'Stockholm': 2
    }
    city_list = list(cities.keys())
    city_index = {city: idx for idx, city in enumerate(city_list)}

    # Direct flights (bidirectional)
    direct_flights = [
        ('Hamburg', 'Stockholm'),
        ('Vienna', 'Stockholm'),
        ('Paris', 'Edinburgh'),
        ('Riga', 'Barcelona'),
        ('Paris', 'Riga'),
        ('Krakow', 'Barcelona'),
        ('Edinburgh', 'Stockholm'),
        ('Paris', 'Krakow'),
        ('Krakow', 'Stockholm'),
        ('Riga', 'Edinburgh'),
        ('Barcelona', 'Stockholm'),
        ('Paris', 'Stockholm'),
        ('Krakow', 'Edinburgh'),
        ('Vienna', 'Hamburg'),
        ('Paris', 'Hamburg'),
        ('Riga', 'Stockholm'),
        ('Hamburg', 'Barcelona'),
        ('Vienna', 'Barcelona'),
        ('Krakow', 'Vienna'),
        ('Riga', 'Hamburg'),
        ('Barcelona', 'Edinburgh'),
        ('Paris', 'Barcelona'),
        ('Hamburg', 'Edinburgh'),
        ('Paris', 'Vienna'),
        ('Vienna', 'Riga')
    ]

    # Create bidirectional flight connections
    flight_connections = set()
    for a, b in direct_flights:
        flight_connections.add((a, b))
        flight_connections.add((b, a))

    # Create solver
    s = Solver()

    # Day variables (1-16)
    days = [Int(f'day_{i}') for i in range(1, 17)]
    for day in days:
        s.add(day >= 0, day < len(city_list))

    # Fixed constraints
    # Paris on days 1-2 (wedding)
    s.add(days[0] == city_index['Paris'])
    s.add(days[1] == city_index['Paris'])

    # Hamburg conference on days 10-11
    s.add(days[9] == city_index['Hamburg'])
    s.add(days[10] == city_index['Hamburg'])

    # Meet friend in Edinburgh between days 12-15
    s.add(Or([days[i] == city_index['Edinburgh'] for i in range(11, 15)]))

    # Visit relatives in Stockholm on days 15-16
    s.add(days[14] == city_index['Stockholm'])
    s.add(days[15] == city_index['Stockholm'])

    # Flight transitions
    for i in range(15):
        current = days[i]
        next_day = days[i+1]
        s.add(Or(
            current == next_day,  # Stay in same city
            # Or take a direct flight
            Or([And(current == city_index[a], next_day == city_index[b])
                for a, b in flight_connections])
        ))

    # Total days per city
    for city, required_days in cities.items():
        s.add(Sum([If(days[i] == city_index[city], 1, 0) for i in range(16)]) == required_days)

    # Try to find a solution
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for i in range(16):
            day_num = i + 1
            city_idx = model.evaluate(days[i]).as_long()
            city = city_list[city_idx]
            itinerary.append({"day": day_num, "place": city})
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

# Solve and print
itinerary = solve_itinerary()
print(json.dumps(itinerary, indent=2))