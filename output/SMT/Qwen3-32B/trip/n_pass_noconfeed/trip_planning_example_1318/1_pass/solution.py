import z3
import json

def main():
    solver = z3.Solver()

    city_names = ['Oslo', 'Helsinki', 'Edinburgh', 'Riga', 'Tallinn', 'Budapest', 'Vilnius', 'Porto', 'Geneva']
    durations = [2, 2, 3, 2, 5, 5, 5, 5, 4]

    # Direct flights
    direct_flights_list = [
        ('Porto', 'Oslo'),
        ('Edinburgh', 'Budapest'),
        ('Edinburgh', 'Geneva'),
        ('Riga', 'Tallinn'),
        ('Edinburgh', 'Porto'),
        ('Vilnius', 'Helsinki'),
        ('Tallinn', 'Vilnius'),
        ('Riga', 'Oslo'),
        ('Geneva', 'Oslo'),
        ('Edinburgh', 'Oslo'),
        ('Edinburgh', 'Helsinki'),
        ('Vilnius', 'Oslo'),
        ('Riga', 'Helsinki'),
        ('Budapest', 'Geneva'),
        ('Helsinki', 'Budapest'),
        ('Helsinki', 'Oslo'),
        ('Edinburgh', 'Riga'),
        ('Tallinn', 'Helsinki'),
        ('Geneva', 'Porto'),
        ('Budapest', 'Oslo'),
        ('Helsinki', 'Geneva'),
        ('Riga', 'Vilnius'),
        ('Tallinn', 'Oslo'),
    ]
    allowed_flights = set()
    for a, b in direct_flights_list:
        allowed_flights.add((a, b))
        allowed_flights.add((b, a))

    # Build flight matrix
    flight = [[False] * 9 for _ in range(9)]
    for i in range(9):
        for j in range(9):
            if (city_names[i], city_names[j]) in allowed_flights:
                flight[i][j] = True

    allowed_pairs = []
    for i in range(9):
        for j in range(9):
            if flight[i][j]:
                allowed_pairs.append((i, j))

    # Create variables for order
    order = [z3.Int(f"order_{i}") for i in range(9)]

    # All cities must be unique
    solver.add(z3.Distinct(order))

    # Each city is between 0 and 8
    for o in order:
        solver.add(z3.And(0 <= o, o < 9))

    # Compute duration for each position
    duration_expr = [0] * 9
    for i in range(9):
        expr = 0
        for city_idx in range(9):
            expr = z3.If(order[i] == city_idx, durations[city_idx], expr)
        duration_expr[i] = expr

    # Compute cumulative durations
    cum_dur = [z3.Int(f"cum_dur_{i}") for i in range(9)]
    solver.add(cum_dur[0] == duration_expr[0])
    for i in range(1, 9):
        solver.add(cum_dur[i] == cum_dur[i - 1] + duration_expr[i])

    # Compute start_day for each position
    start_day = [z3.Int(f"start_day_{i}") for i in range(9)]
    solver.add(start_day[0] == 1)
    for i in range(1, 9):
        solver.add(start_day[i] == 1 + cum_dur[i - 1] - i)

    # Add constraints for Oslo and Tallinn
    oslo_idx = 0
    tallinn_idx = 4
    for i in range(9):
        # Oslo must start on day 24
        solver.add(z3.If(order[i] == oslo_idx, start_day[i] == 24, True))
        # Tallinn must start on day <=8
        solver.add(z3.If(order[i] == tallinn_idx, start_day[i] <= 8, True))

    # Add transition constraints
    for i in range(8):
        transitions = []
        for a, b in allowed_pairs:
            transitions.append(z3.And(order[i] == a, order[i + 1] == b))
        solver.add(z3.Or(transitions))

    # Check if the solver can find a solution
    if solver.check() == z3.sat:
        model = solver.model()
        # Extract order
        order_values = [model.evaluate(order[i]).as_long() for i in range(9)]
        # Compute start_day values
        start_day_values = [model.evaluate(start_day[i]).as_long() for i in range(9)]
        # Generate itinerary
        itinerary = []
        for i in range(9):
            city_idx = order_values[i]
            city_name = city_names[city_idx]
            start = start_day_values[i]
            dur = durations[city_idx]
            end = start + dur - 1
            day_range = f"Day {start}-{end}"
            itinerary.append({"day_range": day_range, "place": city_name})
        # Output as JSON
        print(json.dumps({"itinerary": itinerary}))
    else:
        print("No solution found.")

if __name__ == "__main__":
    main()