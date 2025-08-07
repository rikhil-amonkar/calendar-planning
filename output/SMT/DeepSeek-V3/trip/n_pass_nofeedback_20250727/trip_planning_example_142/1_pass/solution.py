from z3 import *

def solve_itinerary():
    # Create a solver instance
    s = Solver()

    # Define the cities: 0 = Madrid, 1 = Dublin, 2 = Tallinn
    cities = {'Madrid': 0, 'Dublin': 1, 'Tallinn': 2}
    inv_cities = {v: k for k, v in cities.items()}

    # Variables for each day (1-7)
    days = [Int(f'day_{i}') for i in range(1, 8)]

    # Each day must be 0, 1, or 2
    for day in days:
        s.add(Or(day == 0, day == 1, day == 2))

    # Flight constraints: transitions must be between connected cities
    for i in range(6):  # days 1..6 to days 2..7
        current = days[i]
        next_day = days[i+1]
        # Possible transitions:
        # Madrid <-> Dublin, Dublin <-> Tallinn
        s.add(Or(
            current == next_day,  # stay in the same city
            And(current == 0, next_day == 1),  # Madrid to Dublin
            And(current == 1, next_day == 0),  # Dublin to Madrid
            And(current == 1, next_day == 2),  # Dublin to Tallinn
            And(current == 2, next_day == 1)   # Tallinn to Dublin
        ))

    # Total days per city
    madrid_days = Sum([If(d == 0, 1, 0) for d in days])
    dublin_days = Sum([If(d == 1, 1, 0) for d in days])
    tallinn_days = Sum([If(d == 2, 1, 0) for d in days])

    s.add(madrid_days == 4)
    s.add(dublin_days == 3)
    s.add(tallinn_days == 2)

    # Workshop constraint: Tallinn must be on day 6 or 7 (or both)
    s.add(Or(days[5] == 2, days[6] == 2))

    # Check if the problem is satisfiable
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