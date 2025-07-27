from z3 import *

def solve_itinerary():
    s = Solver()

    days = 17
    cities = ['Naples', 'Vienna', 'Vilnius']
    city_map = {'Naples': 0, 'Vienna': 1, 'Vilnius': 2}
    day_city = [Int(f'day_{i}_city') for i in range(1, days + 1)]

    for day in range(days):
        s.add(day_city[day] >= 0, day_city[day] <= 2)

    for day in range(5):
        s.add(day_city[day] == 0)

    for day in range(5, days):
        s.add(day_city[day] != 0)

    vilnius_days = Sum([If(day_city[i] == 2, 1, 0) for i in range(days)])
    vienna_days = Sum([If(day_city[i] == 1, 1, 0) for i in range(days)])

    s.add(vilnius_days == 7)
    s.add(vienna_days == 7)

    for i in range(days - 1):
        current_city = day_city[i]
        next_city = day_city[i + 1]
        s.add(Or(
            And(current_city == 0, next_city == 1),
            And(current_city == 1, next_city == 0),
            And(current_city == 1, next_city == 2),
            And(current_city == 2, next_city == 1),
            current_city == next_city
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