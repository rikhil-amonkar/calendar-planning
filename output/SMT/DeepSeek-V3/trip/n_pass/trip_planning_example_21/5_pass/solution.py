from z3 import *

def solve_trip_planning():
    s = Solver()

    # Days and cities
    days = 10
    Day = [i + 1 for i in range(days)]
    Mykonos, Vienna, Venice = 0, 1, 2
    cities = {0: 'Mykonos', 1: 'Vienna', 2: 'Venice'}

    # Decision variables
    city_vars = [Int(f'day_{day}_city') for day in Day]
    for day in Day:
        s.add(And(city_vars[day - 1] >= 0, city_vars[day - 1] <= 2))

    # Count days in each city
    venice_days = Sum([If(city_vars[day - 1] == Venice, 1, 0) for day in Day])
    mykonos_days = Sum([If(city_vars[day - 1] == Mykonos, 1, 0) for day in Day])
    vienna_days = Sum([If(city_vars[day - 1] == Vienna, 1, 0) for day in Day])

    s.add(venice_days == 6)
    s.add(mykonos_days == 2)
    s.add(vienna_days == 4)

    # Workshop constraint (Venice between days 5-10)
    s.add(Or([city_vars[day - 1] == Venice for day in range(5, 11)]))

    # Flight transition constraints
    for i in range(len(Day) - 1):
        current = city_vars[i]
        next_c = city_vars[i + 1]
        s.add(Or(
            current == next_c,  # Stay in same city
            And(current == Mykonos, next_c == Vienna),
            And(current == Vienna, next_c == Mykonos),
            And(current == Vienna, next_c == Venice),
            And(current == Venice, next_c == Vienna)
        ))

    # Additional constraint: Must start in one city and end in another
    # This helps break symmetry in the solution space
    s.add(Or(
        city_vars[0] == Mykonos,
        city_vars[0] == Vienna,
        city_vars[0] == Venice
    ))
    s.add(Or(
        city_vars[-1] == Mykonos,
        city_vars[-1] == Vienna,
        city_vars[-1] == Venice
    ))

    if s.check() == sat:
        model = s.model()
        itinerary = []
        for day in Day:
            city_val = model.evaluate(city_vars[day - 1])
            itinerary.append({'day': day, 'place': cities[int(str(city_val))]})
        return {'itinerary': itinerary}
    else:
        return {"error": "No valid itinerary found"}

result = solve_trip_planning()
import json
print(json.dumps(result, indent=2))