from z3 import *

def solve_itinerary():
    # Cities encoding
    cities = {
        'Split': 0,
        'Helsinki': 1,
        'Reykjavik': 2,
        'Vilnius': 3,
        'Geneva': 4
    }
    inv_cities = {v: k for k, v in cities.items()}

    # Direct flights: adjacency list
    direct_flights = {
        0: [1, 3, 4],  # Split: Helsinki, Vilnius, Geneva
        1: [0, 2, 3, 4],  # Helsinki: Split, Reykjavik, Vilnius, Geneva
        2: [1],  # Reykjavik: Helsinki
        3: [0, 1],  # Vilnius: Split, Helsinki
        4: [0, 1]   # Geneva: Split, Helsinki
    }

    s = Solver()

    # Variables: day 1 to day 12, each can be one of the cities
    days = [Int(f'day_{i}') for i in range(1, 13)]
    for day in days:
        s.add(day >= 0, day <= 4)  # Each day's value is a city code

    # Constraints for transitions: consecutive days must be same city or connected by direct flight
    for i in range(len(days) - 1):
        current = days[i]
        next_day = days[i + 1]
        # Either stay in the same city or move to a directly connected city
        s.add(Or(
            current == next_day,
            Or([And(current == city, next_day in direct_flights[city]) for city in direct_flights])
        ))

    # Count days per city
    split_days = Sum([If(days[i] == cities['Split'], 1, 0) for i in range(12)])
    helsinki_days = Sum([If(days[i] == cities['Helsinki'], 1, 0) for i in range(12)])
    reykjavik_days = Sum([If(days[i] == cities['Reykjavik'], 1, 0) for i in range(12)])
    vilnius_days = Sum([If(days[i] == cities['Vilnius'], 1, 0) for i in range(12)])
    geneva_days = Sum([If(days[i] == cities['Geneva'], 1, 0) for i in range(12)])

    # Add constraints for required days per city
    s.add(split_days == 2)
    s.add(helsinki_days == 2)
    s.add(reykjavik_days == 3)
    s.add(vilnius_days == 3)
    s.add(geneva_days == 6)

    # Reykjavik must include at least one day between 10 and 12 (days are 1-based)
    s.add(Or([days[i] == cities['Reykjavik'] for i in range(9, 12)]))

    # Vilnius must include at least one day between 7 and 9 (days are 1-based)
    s.add(Or([days[i] == cities['Vilnius'] for i in range(6, 9)]))

    # Check and get model
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for i in range(12):
            city_code = m.evaluate(days[i]).as_long()
            itinerary.append({'day': i + 1, 'place': inv_cities[city_code]})
        return {'itinerary': itinerary}
    else:
        return {'error': 'No valid itinerary found'}

result = solve_itinerary()
import json
print(json.dumps(result, indent=2))