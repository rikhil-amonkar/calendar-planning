from z3 import *

def solve_itinerary():
    s = Solver()

    days = 17
    cities = ['Naples', 'Vienna', 'Vilnius']
    city_map = {'Naples': 0, 'Vienna': 1, 'Vilnius': 2}
    day_city = [Int(f'day_{i}_city') for i in range(1, days + 1)]

    # Each day must be one of the three cities
    for day in range(days):
        s.add(day_city[day] >= 0, day_city[day] <= 2)

    # Days 1-5 must be Naples
    for day in range(5):
        s.add(day_city[day] == 0)

    # Days after 5 cannot be Naples
    for day in range(5, days):
        s.add(day_city[day] != 0)

    # Count days in each city
    naples_days = Sum([If(day_city[i] == 0, 1, 0) for i in range(days)])
    vienna_days = Sum([If(day_city[i] == 1, 1, 0) for i in range(days)])
    vilnius_days = Sum([If(day_city[i] == 2, 1, 0) for i in range(days)])

    # Total days requirements
    s.add(naples_days == 5)
    s.add(vienna_days == 7)
    s.add(vilnius_days == 7)

    # Count flight days (where city changes)
    flight_days = Sum([If(day_city[i] != day_city[i+1], 1, 0) for i in range(days-1)])
    s.add(flight_days == 2)  # Exactly 2 flight days

    # Only allow direct flights
    for i in range(days - 1):
        current = day_city[i]
        next = day_city[i+1]
        s.add(Or(
            And(current == 0, next == 1),  # Naples to Vienna
            And(current == 1, next == 0),  # Vienna to Naples
            And(current == 1, next == 2),  # Vienna to Vilnius
            And(current == 2, next == 1),  # Vilnius to Vienna
            current == next                 # Stay in same city
        ))

    if s.check() == sat:
        m = s.model()
        itinerary = []
        for day in range(1, days + 1):
            city_code = m.evaluate(day_city[day - 1]).as_long()
            city = cities[city_code]
            itinerary.append({"day": day, "place": city})
        return {'itinerary': itinerary}
    else:
        return {"error": "No valid itinerary found"}

result = solve_itinerary()
import json
print(json.dumps(result, indent=2))