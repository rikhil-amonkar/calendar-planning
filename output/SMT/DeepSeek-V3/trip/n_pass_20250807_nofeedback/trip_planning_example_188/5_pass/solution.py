from z3 import *

def solve_itinerary():
    s = Solver()

    # Cities: 1 = Brussels, 2 = Barcelona, 3 = Split
    days = 12
    city = [Int(f'city_{i+1}') for i in range(days)]

    # Each day must be one of the three cities
    for i in range(days):
        s.add(Or(city[i] == 1, city[i] == 2, city[i] == 3))

    # Days 1 and 2 must be Brussels
    s.add(city[0] == 1)
    s.add(city[1] == 1)

    # Total days in each city
    brussels_days = Sum([If(city[i] == 1, 1, 0) for i in range(days)])
    barcelona_days = Sum([If(city[i] == 2, 1, 0) for i in range(days)])
    split_days = Sum([If(city[i] == 3, 1, 0) for i in range(days)])

    s.add(brussels_days == 2)
    s.add(barcelona_days == 7)
    s.add(split_days == 5)

    # Flight constraints
    for i in range(days - 1):
        current = city[i]
        next_c = city[i + 1]
        s.add(Or(
            current == next_c,  # stay in same city
            And(current == 1, next_c == 2),  # Brussels to Barcelona
            And(current == 2, next_c == 1),  # Barcelona to Brussels
            And(current == 2, next_c == 3),  # Barcelona to Split
            And(current == 3, next_c == 2)   # Split to Barcelona
        ))

    # No direct Brussels-Split flights
    for i in range(days - 1):
        s.add(Not(And(city[i] == 1, city[i+1] == 3)))
        s.add(Not(And(city[i] == 3, city[i+1] == 1)))

    if s.check() == sat:
        m = s.model()
        itinerary = []
        city_names = {1: 'Brussels', 2: 'Barcelona', 3: 'Split'}
        for i in range(days):
            day = i + 1
            c = m.evaluate(city[i])
            itinerary.append({'day': day, 'place': city_names[int(str(c))]})
        return {'itinerary': itinerary}
    else:
        return {'error': 'No valid itinerary found'}

# Generate and print the itinerary
itinerary = solve_itinerary()
import json
print(json.dumps(itinerary, indent=2))