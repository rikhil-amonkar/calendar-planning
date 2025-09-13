from z3 import *

import json

def main():
    cities = ['Frankfurt', 'Salzburg', 'Athens', 'Reykjavik', 'Bucharest', 'Valencia', 'Vienna', 'Amsterdam', 'Stockholm', 'Riga']
    durations = [4, 5, 5, 5, 3, 2, 5, 3, 3, 3]
    city_indices = {city: idx for idx, city in enumerate(cities)}

    # Direct flights pairs
    direct_flights_pairs = [
        (5, 0), (0, 5),  # Valencia-Frankfurt
        (6, 4), (4, 6),  # Vienna-Bucharest
        (5, 2), (2, 5),  # Valencia-Athens
        (2, 4), (4, 2),  # Athens-Bucharest
        (9, 0), (0, 9),  # Riga-Frankfurt
        (8, 2), (2, 8),  # Stockholm-Athens
        (7, 4), (4, 7),  # Amsterdam-Bucharest
        (2, 9), (9, 2),  # Athens-Riga
        (7, 0), (0, 7),  # Amsterdam-Frankfurt
        (8, 6), (6, 8),  # Stockholm-Vienna
        (6, 9), (9, 6),  # Vienna-Riga
        (7, 3), (3, 7),  # Amsterdam-Reykjavik
        (3, 0), (0, 3),  # Reykjavik-Frankfurt
        (8, 7), (7, 8),  # Stockholm-Amsterdam
        (7, 5), (5, 7),  # Amsterdam-Valencia
        (6, 0), (0, 6),  # Vienna-Frankfurt
        (5, 4), (4, 5),  # Valencia-Bucharest
        (4, 0), (0, 4),  # Bucharest-Frankfurt
        (8, 0), (0, 8),  # Stockholm-Frankfurt
        (5, 6), (6, 5),  # Valencia-Vienna
        (3, 2), (2, 3),  # Reykjavik-Athens
        (0, 1), (1, 0),  # Frankfurt-Salzburg
        (7, 6), (6, 7),  # Amsterdam-Vienna
        (8, 3), (3, 8),  # Stockholm-Reykjavik
        (7, 9), (9, 7),  # Amsterdam-Riga
        (8, 9), (9, 8),  # Stockholm-Riga
        (6, 3), (3, 6),  # Vienna-Reykjavik
        (7, 2), (2, 7),  # Amsterdam-Athens
        (2, 0), (0, 2),  # Athens-Frankfurt
        (6, 2), (2, 6),  # Vienna-Athens
        (9, 4), (4, 9),  # Riga-Bucharest
    ]

    s = Solver()

    # Define order variables
    order = [Int(f'order_{i}') for i in range(10)]
    s.add(Distinct(order))
    for i in range(10):
        s.add(And(0 <= order[i], order[i] <= 9))

    # Define sum_dur variables
    sum_dur = [Int(f'sum_dur_{i}') for i in range(11)]  # sum_dur[0] to sum_dur[10]
    s.add(sum_dur[0] == 0)
    for i in range(1, 11):
        s.add(sum_dur[i] == sum_dur[i-1] + durations[order[i-1]])

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
        # Build s_c_expr using nested If statements
        def build_s_c_expr(c):
            expr = 0
            for i in range(10):
                condition = (pos[c] == i)
                value = 1 + sum_dur[i] - i
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
        # Extract order values
        order_vals = [model.evaluate(order[i]).as_long() for i in range(10)]
        # Compute sum_dur_vals based on order_vals
        sum_dur_vals = [0] * 11
        for i in range(1, 11):
            sum_dur_vals[i] = sum_dur_vals[i-1] + durations[order_vals[i-1]]
        # Generate itinerary
        itinerary = []
        for i in range(10):
            start_day = 1 + sum_dur_vals[i] - i
            duration = durations[order_vals[i]]
            end_day = start_day + duration - 1
            city = cities[order_vals[i]]
            day_range = f"Day {start_day}-{end_day}"
            itinerary.append({"day_range": day_range, "place": city})
        # Output as JSON
        print(json.dumps({"itinerary": itinerary}))
    else:
        print(json.dumps({"error": "No solution found"}))

if __name__ == "__main__":
    main()