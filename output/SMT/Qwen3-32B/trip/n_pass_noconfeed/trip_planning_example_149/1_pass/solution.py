import json
from z3 import *

def main():
    solver = Solver()

    c1, c2, c3 = Ints('c1 c2 c3')
    d1, d2, d3 = Ints('d1 d2 d3')

    # All cities are distinct
    solver.add(Distinct(c1, c2, c3))

    # Allowed transitions between c1 and c2
    allowed_transitions_1 = Or(
        And(c1 == 0, c2 == 1),
        And(c1 == 1, c2 == 0),
        And(c1 == 0, c2 == 2),
        And(c1 == 2, c2 == 0)
    )
    solver.add(allowed_transitions_1)

    # Allowed transitions between c2 and c3
    allowed_transitions_2 = Or(
        And(c2 == 0, c3 == 1),
        And(c2 == 1, c3 == 0),
        And(c2 == 0, c3 == 2),
        And(c2 == 2, c3 == 0)
    )
    solver.add(allowed_transitions_2)

    # Duration constraints based on city
    solver.add(Implies(c1 == 0, d1 == 3))
    solver.add(Implies(c1 == 1, d1 == 3))
    solver.add(Implies(c1 == 2, d1 == 6))

    solver.add(Implies(c2 == 0, d2 == 3))
    solver.add(Implies(c2 == 1, d2 == 3))
    solver.add(Implies(c2 == 2, d2 == 6))

    solver.add(Implies(c3 == 0, d3 == 3))
    solver.add(Implies(c3 == 1, d3 == 3))
    solver.add(Implies(c3 == 2, d3 == 6))

    # Total duration constraint
    solver.add(d1 + d2 + d3 == 12)

    # Santorini is the third city
    solver.add(c3 == 2)

    # Duration constraint for Santorini's start day
    solver.add(d1 + d2 == 6)

    if solver.check() == sat:
        model = solver.model()
        c1_val = model[c1].as_long()
        c2_val = model[c2].as_long()
        c3_val = model[c3].as_long()
        d1_val = model[d1].as_long()
        d2_val = model[d2].as_long()
        d3_val = model[d3].as_long()

        city_names = {0: 'London', 1: 'Istanbul', 2: 'Santorini'}
        itinerary = []

        # First city
        start_day_1 = 1
        end_day_1 = start_day_1 + d1_val - 1
        itinerary.append({
            'day_range': f"Day {start_day_1}-{end_day_1}",
            'place': city_names[c1_val]
        })

        # Second city
        start_day_2 = end_day_1
        end_day_2 = start_day_2 + d2_val - 1
        itinerary.append({
            'day_range': f"Day {start_day_2}-{end_day_2}",
            'place': city_names[c2_val]
        })

        # Third city
        start_day_3 = end_day_2
        end_day_3 = start_day_3 + d3_val - 1
        itinerary.append({
            'day_range': f"Day {start_day_3}-{end_day_3}",
            'place': city_names[c3_val]
        })

        print(json.dumps({'itinerary': itinerary}, indent=2))
    else:
        print("No solution found.")

if __name__ == "__main__":
    main()