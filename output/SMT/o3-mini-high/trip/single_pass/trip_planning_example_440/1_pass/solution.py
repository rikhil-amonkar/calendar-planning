from z3 import *
import json

def main():
    # Create a solver
    solver = Solver()

    # We represent each city by an integer:
    # 0: Geneva (6 days)
    # 1: Helsinki (2 days)
    # 2: Reykjavik (3 days)
    # 3: Vilnius (3 days)
    # 4: Split (2 days)
    # There will be 5 segments (one per city visited in order).
    order = [Int(f"order_{i}") for i in range(5)]
    for o in order:
        solver.add(o >= 0, o <= 4)
    solver.add(Distinct(order))

    # Define the required duration for each city using an If-expression.
    def duration_expr(city):
        return If(city == 0, 6,
               If(city == 1, 2,
               If(city == 2, 3,
               If(city == 3, 3,   # Vilnius: 3 days
                  2))))      # Split: 2 days

    # For each segment i, let S[i] be the start day and E[i] the end day (inclusive).
    # When flying from one segment to the next, the flight day counts for both cities.
    S = [Int(f"S_{i}") for i in range(5)]
    E = [Int(f"E_{i}") for i in range(5)]
    for i in range(5):
        solver.add(E[i] == S[i] + duration_expr(order[i]) - 1)

    # The itinerary days form one continuous timeline of 12 days.
    # The first segment must start on Day 1.
    solver.add(S[0] == 1)
    # For consecutive segments, the next starts on the same day the previous one ends.
    for i in range(4):
        solver.add(S[i+1] == E[i])
    # The last segment’s end day must be Day 12.
    solver.add(E[4] == 12)

    # Allowed direct flight connections (bidirectional).
    # Each tuple (a, b) means you can fly from city a to city b on the transition day.
    allowed_pairs = [
      (0, 1),  # Geneva - Helsinki
      (1, 0),
      (0, 4),  # Geneva - Split
      (4, 0),
      (1, 2),  # Helsinki - Reykjavik
      (2, 1),
      (3, 1),  # Vilnius - Helsinki
      (1, 3),
      (4, 3),  # Split - Vilnius
      (3, 4),
      (1, 4),  # Split and Helsinki (both directions are allowed)
      (4, 1)
    ]
    # For every adjacent segment in the order, enforce that a direct flight exists.
    for i in range(4):
        pair_possible = []
        for (a, b) in allowed_pairs:
            pair_possible.append(And(order[i] == a, order[i+1] == b))
        solver.add(Or(pair_possible))

    # Special constraint: Because the only connection to/from Reykjavik is via Helsinki,
    # whenever Helsinki (1) is followed immediately by another city it must be Reykjavik (2).
    for i in range(4):
        solver.add(Implies(order[i] == 1, order[i+1] == 2))

    # Wedding in Reykjavik:
    # If Reykjavik (2) is visited, the visit (which lasts 3 days) must cover at least one day
    # between Day 10 and Day 12.
    for i in range(5):
        solver.add(Implies(order[i] == 2, And(S[i] <= 12, E[i] >= 10)))

    # Visiting relatives in Vilnius:
    # If Vilnius (3) is visited, the 3‐day stay must include at least one day in the range 7–9.
    for i in range(5):
        solver.add(Implies(order[i] == 3, And(S[i] <= 9, E[i] >= 7)))

    # Solve the constraints.
    if solver.check() == sat:
        m = solver.model()
        # Prepare a mapping for city names.
        city_names = {
            0: "Geneva",
            1: "Helsinki",
            2: "Reykjavik",
            3: "Vilnius",
            4: "Split"
        }
        itinerary = []
        for i in range(5):
            start_day = m[S[i]].as_long()
            end_day   = m[E[i]].as_long()
            city      = city_names[m[order[i]].as_long()]
            # We output the segment as a mapping from the day interval to the city.
            itinerary.append({
                "day_range": f"{start_day}-{end_day}",
                "place": city
            })

        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found.")

if __name__ == "__main__":
    main()