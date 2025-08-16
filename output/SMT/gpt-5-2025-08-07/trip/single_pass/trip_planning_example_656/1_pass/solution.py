from z3 import *
import json

def solve_itinerary():
    # City indices
    R, I, E, O, S, B = 0, 1, 2, 3, 4, 5
    city_names = {
        R: "Reykjavik",
        I: "Istanbul",
        E: "Edinburgh",
        O: "Oslo",
        S: "Stuttgart",
        B: "Bucharest",
    }

    # Length of stay (in days) for each city
    L = {
        R: 5,
        I: 4,
        E: 5,
        O: 2,
        S: 3,
        B: 5,
    }

    # Allowed direct flights (directed pairs)
    allowed = set()
    # Bucharest <-> Oslo
    allowed.add((B, O)); allowed.add((O, B))
    # Istanbul <-> Oslo
    allowed.add((I, O)); allowed.add((O, I))
    # Reykjavik -> Stuttgart (one-way)
    allowed.add((R, S))
    # Bucharest <-> Istanbul
    allowed.add((B, I)); allowed.add((I, B))
    # Stuttgart <-> Edinburgh
    allowed.add((S, E)); allowed.add((E, S))
    # Istanbul <-> Edinburgh
    allowed.add((I, E)); allowed.add((E, I))
    # Oslo <-> Reykjavik
    allowed.add((O, R)); allowed.add((R, O))
    # Istanbul <-> Stuttgart
    allowed.add((I, S)); allowed.add((S, I))
    # Oslo <-> Edinburgh
    allowed.add((O, E)); allowed.add((E, O))

    solver = Solver()

    # Order variables: which city is visited at each position 0..5
    order = [Int(f"order_{k}") for k in range(6)]
    # Domain constraints
    for k in range(6):
        solver.add(And(order[k] >= 0, order[k] <= 5))
    # All cities exactly once (permutation of 0..5)
    solver.add(Distinct(order))

    # Start day at each position
    s_pos = [Int(f"s_{k}") for k in range(6)]

    # Helper: piecewise length for a city variable
    def len_of(city_var):
        return Sum([If(city_var == c, L[c], 0) for c in range(6)])

    # Chain constraints with overlap rule:
    # - First city starts on day 1
    solver.add(s_pos[0] == 1)
    # - Next city starts on the same day the previous city ends (overlap day)
    for k in range(5):
        solver.add(s_pos[k+1] == s_pos[k] + len_of(order[k]) - 1)
    # - Last city must end on day 19
    solver.add(s_pos[5] + len_of(order[5]) - 1 == 19)

    # Ensure s_pos days are within bounds
    for k in range(6):
        solver.add(And(s_pos[k] >= 1, s_pos[k] <= 19))

    # Direct flight constraints between consecutive cities in the sequence
    for k in range(5):
        solver.add(Or([And(order[k] == a, order[k+1] == b) for (a, b) in allowed]))

    # Specific timing constraints:
    # - Istanbul for 4 days and meet friends between day 5 and day 8 => Istanbul is exactly days 5-8
    #   So the start day at the position where Istanbul appears is 5
    for k in range(6):
        solver.add(Implies(order[k] == I, s_pos[k] == 5))

    # - Oslo for 2 days and visit relatives between day 8 and day 9 => Oslo is exactly days 8-9
    for k in range(6):
        solver.add(Implies(order[k] == O, s_pos[k] == 8))

    if solver.check() != sat:
        raise RuntimeError("No feasible itinerary found.")

    model = solver.model()

    # Extract the sequence and start days
    order_vals = [model.evaluate(order[k]).as_long() for k in range(6)]
    s_vals = [model.evaluate(s_pos[k]).as_long() for k in range(6)]
    # Compute end days for convenience
    e_vals = [s_vals[k] + L[order_vals[k]] - 1 for k in range(6)]

    # Build a day -> city mapping:
    # For each day d, pick the city of the segment with the largest k such that s_pos[k] <= d
    itinerary = []
    for day in range(1, 20):
        # find the segment index with maximal start <= day
        k_best = max([k for k in range(6) if s_vals[k] <= day])
        city_idx = order_vals[k_best]
        itinerary.append({"day": day, "place": city_names[city_idx]})

    # Output JSON
    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False, indent=2))

if __name__ == "__main__":
    solve_itinerary()