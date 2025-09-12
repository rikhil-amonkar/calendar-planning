import json
from z3 import *

def main():
    s = Solver()

    c1, c2, c3 = Ints('c1 c2 c3')
    start_1, end_1 = Ints('start_1 end_1')
    start_2, end_2 = Ints('start_2 end_2')
    start_3, end_3 = Ints('start_3 end_3')

    # Constraints
    s.add(c1 == 0)  # First city is Bucharest
    s.add(Distinct(c1, c2, c3))

    # Allowed transitions between c1 and c2
    allowed_transitions_c1_c2 = Or(
        And(c1 == 0, c2 == 1),
        And(c1 == 1, c2 == 0),
        And(c1 == 1, c2 == 2),
        And(c1 == 2, c2 == 1)
    )
    s.add(allowed_transitions_c1_c2)

    # Allowed transitions between c2 and c3
    allowed_transitions_c2_c3 = Or(
        And(c2 == 0, c3 == 1),
        And(c2 == 1, c3 == 0),
        And(c2 == 1, c3 == 2),
        And(c2 == 2, c3 == 1)
    )
    s.add(allowed_transitions_c2_c3)

    # Duration constraints
    s.add(start_1 == 1)
    s.add(end_1 == start_1 + 7 - 1)  # Bucharest duration is 7 days
    s.add(start_2 == end_1)
    s.add(end_2 == start_2 + 7 - 1)  # Lyon duration is 7 days
    s.add(start_3 == end_2)
    s.add(end_3 == start_3 + 4 - 1)  # Porto duration is 4 days
    s.add(end_3 == 16)

    if s.check() == sat:
        m = s.model()
        city_names = {0: 'Bucharest', 1: 'Lyon', 2: 'Porto'}
        cities_order = [m[c1].as_long(), m[c2].as_long(), m[c3].as_long()]

        # Get the start and end days
        start_1_val = m[start_1].as_long()
        end_1_val = m[end_1].as_long()
        start_2_val = m[start_2].as_long()
        end_2_val = m[end_2].as_long()
        start_3_val = m[start_3].as_long()
        end_3_val = m[end_3].as_long()

        itinerary = [
            {"day_range": f"Day {start_1_val}-{end_1_val}", "place": city_names[cities_order[0]]},
            {"day_range": f"Day {start_2_val}-{end_2_val}", "place": city_names[cities_order[1]]},
            {"day_range": f"Day {start_3_val}-{end_3_val}", "place": city_names[cities_order[2]]}
        ]

        print(json.dumps({"itinerary": itinerary}, indent=2))
    else:
        print(json.dumps({"error": "No solution found"}))

if __name__ == "__main__":
    main()