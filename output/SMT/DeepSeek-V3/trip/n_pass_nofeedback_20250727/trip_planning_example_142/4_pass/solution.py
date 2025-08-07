from z3 import *

def solve_itinerary():
    s = Solver()

    # City mapping
    cities = {'Madrid': 0, 'Dublin': 1, 'Tallinn': 2}
    inv_cities = {v: k for k, v in cities.items()}

    # Day variables (1-7)
    days = [Int(f'day_{i}') for i in range(1, 8)]

    # Each day must be a valid city
    for day in days:
        s.add(Or(day == 0, day == 1, day == 2))

    # Flight transition constraints
    for i in range(6):
        current = days[i]
        next_day = days[i+1]
        s.add(Or(
            current == next_day,  # Stay in same city
            And(current == 0, next_day == 1),  # Madrid -> Dublin
            And(current == 1, next_day == 0),  # Dublin -> Madrid
            And(current == 1, next_day == 2),  # Dublin -> Tallinn
            And(current == 2, next_day == 1)   # Tallinn -> Dublin
        ))

    # Total days in each city
    s.add(Sum([If(d == 0, 1, 0) for d in days]) == 4)  # Madrid
    s.add(Sum([If(d == 1, 1, 0) for d in days]) == 3)  # Dublin
    s.add(Sum([If(d == 2, 1, 0) for d in days]) == 2)  # Tallinn

    # Workshop constraint (Tallinn on day 6 or 7)
    s.add(Or(days[5] == 2, days[6] == 2))

    # Additional constraints to guide the solver
    # Start in Madrid (most flexible starting point)
    s.add(days[0] == 0)
    # Ensure we don't have consecutive Tallinn days (since we only have 2 days)
    for i in range(5):
        s.add(Not(And(days[i] == 2, days[i+1] == 2)))

    # Solve and return the itinerary
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for i in range(7):
            day_num = i + 1
            city_code = model.evaluate(days[i]).as_long()
            city_name = inv_cities[city_code]
            itinerary.append({'day': day_num, 'place': city_name})
        return {'itinerary': itinerary}
    else:
        return {'error': 'No valid itinerary found'}

# Output the solution
import json
solution = solve_itinerary()
print(json.dumps(solution, indent=2))