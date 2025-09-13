import json
from z3 import *

def main():
    solver = Solver()

    start_v = Int('start_v')
    start_s = Int('start_s')
    start_m = Int('start_m')
    start_t = Int('start_t')

    # Duration constraints based on required days
    # Vilnius: 4 days => end_v = start_v + 3
    # Split: 5 days => end_s = start_s + 4
    # Madrid: 6 days => end_m = start_m + 5
    # Santorini: 2 days => end_t = start_t + 1

    # Transition constraints
    solver.add(start_s == start_v + 3)  # end_v is start_v + 3, which is start_s
    solver.add(start_m == start_s + 4)  # end_s is start_s + 4
    solver.add(start_t == start_m + 5)  # end_m is start_m + 5
    # Santorini must start on day 13 to cover days 13-14
    solver.add(start_t == 13)

    # Ensure the first day is at least 1
    solver.add(start_v >= 1)

    if solver.check() == sat:
        model = solver.model()
        start_v_val = model[start_v].as_long()
        start_s_val = model[start_s].as_long()
        start_m_val = model[start_m].as_long()
        start_t_val = model[start_t].as_long()

        itinerary = [
            {"day_range": f"Day {start_v_val}-{start_v_val + 3}", "place": "Vilnius"},
            {"day_range": f"Day {start_s_val}-{start_s_val + 4}", "place": "Split"},
            {"day_range": f"Day {start_m_val}-{start_m_val + 5}", "place": "Madrid"},
            {"day_range": f"Day {start_t_val}-{start_t_val + 1}", "place": "Santorini"}
        ]

        print(json.dumps({"itinerary": itinerary}, indent=2))
    else:
        print(json.dumps({"error": "No solution found"}))

if __name__ == "__main__":
    main()