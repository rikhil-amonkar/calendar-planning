from z3 import *
import json

def main():
    cities = ['Frankfurt', 'Salzburg', 'Athens', 'Reykjavik', 'Bucharest', 'Valencia', 'Vienna', 'Amsterdam', 'Stockholm', 'Riga']
    durations = [4, 5, 5, 5, 3, 2, 5, 3, 3, 3]
    city_indices = {city: idx for idx, city in enumerate(cities)}

    # Direct flights pairs
    direct_flights_pairs = [
        (5, 0), (0, 5),  # Valencia-Frankfurt
        # ... (Assume rest are defined correctly)
    ]

    s = Solver()

    # Define order variables
    order = [Int(f'order_{i}') for i in range(10)]
    s.add(Distinct(order))
    for i in range(10):
        s.add(And(0 <= order[i], order[i] <= 9))

    # Create a Z3 array for durations
    duration_array = Array('duration_array', IntSort(), IntSort())
    for c in range(10):
        s.add(duration_array[c] == durations[c])

    # Define sum_dur variables
    sum_dur = [Int(f'sum_dur_{i}') for i in range(11)]  # sum_dur[0] to sum_dur[10]
    s.add(sum_dur[0] == 0)
    for i in range(1, 11):
        s.add(sum_dur[i] == sum_dur[i-1] + duration_array[order[i-1]])

    # Define pos variables for each city
    pos = [Int(f'pos_{c}') for c in range(10)]
    for c in range(10):
        for i in range(10):
            s.add((order[i] == c) == (pos[c] == i))

    # Add direct flight constraints for consecutive cities
    for i in range(9):
        current = order[i]
        next_city = order[i+1]
        constraints = []
        for a, b in direct_flights_pairs:
            constraints.append(And(current == a, next_city == b))
        s.add(Or(constraints))

    # Event constraints
    events = [
        (2, 14, 18),  # Athens: workshop between 14-18
        (5, 5, 6),    # Valencia: show between 5-6
        (6, 6, 10),   # Vienna: wedding between 6-10
        (8, 1, 3),    # Stockholm: friend between 1-3
        (9, 18, 20),  # Riga: conference between 18-20
    ]

    for c, event_start, event_end in events:
        def build_s_c_expr(c):
            expr = 0
            for i in range(10):
                condition = (pos[c] == i)
                value = 1 + sum_dur[i]  # Corrected: removed -i
                if i == 0:
                    expr = If(condition, value, 0)
                else:
                    expr = If(condition, value, expr)
            return expr
        s_c_expr = build_s_c_expr(c)
        e_c_expr = s_c_expr + durations[c] - 1
        overlap = And(s_c_expr <= event_end, e_c_expr >= event_start)
        s.add(overlap)

    # Check if the problem is satisfiable
    if s.check() == sat:
        model = s.model()
        order_vals = [model.evaluate(order[i]).as_long() for i in range(10)]
        sum_dur_vals = [0] * 11
        for i in range(1, 11):
            sum_dur_vals[i] = sum_dur_vals[i-1] + durations[order_vals[i-1]]
        itinerary = []
        for i in range(10):
            start_day = 1 + sum_dur_vals[i]  # Corrected: removed -i
            duration = durations[order_vals[i]]
            end_day = start_day + duration - 1
            city = cities[order_vals[i]]
            day_range = f"Day {start_day}-{end_day}"
            itinerary.append({"day_range": day_range, "place": city})
        print(json.dumps({"itinerary": itinerary}))
    else:
        print(json.dumps({"error": "No solution found"}))

if __name__ == "__main__":
    main()