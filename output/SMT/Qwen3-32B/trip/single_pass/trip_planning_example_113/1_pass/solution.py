from z3 import *

def solve_itinerary():
    solver = Solver()
    days = [Int(f'day_{i+1}') for i in range(12)]  # days[0] is day 1, days[11] is day 12

    # Add transition constraints between cities
    for i in range(11):  # i from 0 to 10 (days 1 to 11)
        prev = days[i]
        curr = days[i+1]
        allowed = Or(
            And(prev == 0, curr == 2),
            And(prev == 2, curr == 0),
            And(prev == 2, curr == 1),
            And(prev == 1, curr == 2)
        )
        solver.add(Implies(prev != curr, allowed))

    # Count constraints for each city
    # Naples (0): 3 days
    count_naples = If(days[0] == 0, 1, 0)
    for i in range(1, 12):  # original days 2 to 12
        prev = days[i-1]
        curr = days[i]
        same = curr == prev
        contribution = If(same, If(curr == 0, 1, 0), If(Or(prev == 0, curr == 0), 1, 0))
        count_naples += contribution
    solver.add(count_naples == 3)

    # Seville (1): 4 days
    count_seville = If(days[0] == 1, 1, 0)
    for i in range(1, 12):
        prev = days[i-1]
        curr = days[i]
        same = curr == prev
        contribution = If(same, If(curr == 1, 1, 0), If(Or(prev == 1, curr == 1), 1, 0))
        count_seville += contribution
    solver.add(count_seville == 4)

    # Milan (2): 7 days
    count_milan = If(days[0] == 2, 1, 0)
    for i in range(1, 12):
        prev = days[i-1]
        curr = days[i]
        same = curr == prev
        contribution = If(same, If(curr == 2, 1, 0), If(Or(prev == 2, curr == 2), 1, 0))
        count_milan += contribution
    solver.add(count_milan == 7)

    # Constraints for days 9-12 (indices 8,9,10,11)
    for i in [8,9,10,11]:
        prev = days[i-1]
        curr = days[i]
        solver.add(Implies(curr == prev, curr == 1))
        solver.add(Implies(curr != prev, Or(prev == 1, curr == 1)))

    if solver.check() == sat:
        model = solver.model()
        itinerary = []
        city_map = {0: 'Naples', 1: 'Seville', 2: 'Milan'}
        for idx, day_var in enumerate(days):
            day_num = idx + 1
            city_val = model[day_var].as_long()
            city_name = city_map[city_val]
            itinerary.append({day_num: city_name})
        return {'itinerary': itinerary}
    else:
        return None

# Call the function and print the JSON
solution = solve_itinerary()
if solution:
    import json
    print(json.dumps(solution, indent=2))
else:
    print("No solution found.")