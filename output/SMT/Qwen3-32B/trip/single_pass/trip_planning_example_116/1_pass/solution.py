from z3 import *

def solve_scheduling():
    solver = Solver()

    # Define the days as integers (0: Split, 1: Santorini, 2: London)
    days = [Int(f'day_{i+1}') for i in range(18)]

    # Constraint: each day is one of the three cities
    for d in days:
        solver.add(Or(d == 0, d == 1, d == 2))

    # Constraint: allowed transitions
    for i in range(17):
        current = days[i]
        next_day = days[i+1]
        solver.add(Or(current == next_day,
                      And(current == 0, next_day == 2),
                      And(current == 2, next_day == 0),
                      And(current == 2, next_day == 1),
                      And(current == 1, next_day == 2)))

    # Constraint: day 12 and day 18 are Santorini (1)
    solver.add(days[11] == 1)  # day 12 is index 11
    solver.add(days[17] == 1)  # day 18 is index 17

    # Constraints for total days in each city
    for c in [0, 1, 2]:
        count_in_itinerary = Sum([If(days[i] == c, 1, 0) for i in range(18)])
        departures = Sum([If(And(days[i] == c, days[i] != days[i+1]), 1, 0) for i in range(17)])
        arrivals = Sum([If(And(days[i+1] == c, days[i] != days[i+1]), 1, 0) for i in range(17)])
        total_transitions = departures + arrivals
        total_days = count_in_itinerary + total_transitions
        if c == 0:
            solver.add(total_days == 6)
        elif c == 1:
            solver.add(total_days == 7)
        else:
            solver.add(total_days == 7)

    if solver.check() == sat:
        model = solver.model()
        itinerary = [model.eval(days[i]).as_long() for i in range(18)]
        # Convert to city names
        city_names = {0: 'Split', 1: 'Santorini', 2: 'London'}
        result = [{'day': i+1, 'city': city_names[city]} for i, city in enumerate(itinerary)]
        return {'itinerary': result}
    else:
        return {'itinerary': []}

# Example usage (this would typically be run in a script)
if __name__ == "__main__":
    solution = solve_scheduling()
    print(solution)