from z3 import *
import json

def main():
    # Create a solver instance
    solver = Solver()

    # We encode cities as integers:
    # 0: Geneva, 1: Paris, 2: Oslo, 3: Porto, 4: Reykjavik
    num_segments = 5

    # Define the itinerary: a permutation of 5 cities, with the first fixed to Geneva.
    cities = [Int(f"city_{i}") for i in range(num_segments)]
    # Start and end day variables for each segment
    s = [Int(f"s_{i}") for i in range(num_segments)]
    e = [Int(f"e_{i}") for i in range(num_segments)]

    # Duration mapping for each city:
    # Geneva: 7 days, Paris: 6 days, Oslo: 5 days, Porto: 7 days, Reykjavik: 2 days.
    def seg_duration(i):
        return If(cities[i] == 0, 7,
               If(cities[i] == 1, 6,
               If(cities[i] == 2, 5,
               If(cities[i] == 3, 7, 2))))
    
    # Constraint 1: The itinerary is a permutation and the trip visits 5 distinct cities.
    solver.add(cities[0] == 0)  # Must start in Geneva (so that conference on Day 1 and Day 7 occur in Geneva)
    for i in range(1, num_segments):
        # The other cities can only be from Paris (1), Oslo (2), Porto (3), or Reykjavik (4)
        solver.add(And(cities[i] >= 1, cities[i] <= 4))
    solver.add(Distinct(cities))

    # Constraint 2: Set up start/end days so that flight days count double.
    # If you fly from city A to city B on day X, then day X belongs to both segments.
    # We'll define for segment 0: s_0 = 1 and e_0 = s_0 + duration - 1.
    solver.add(s[0] == 1)
    for i in range(num_segments):
        solver.add(e[i] == s[i] + seg_duration(i) - 1)
        if i > 0:
            solver.add(s[i] == e[i-1])
    # Total trip length must be exactly 23 days.
    solver.add(e[num_segments-1] == 23)

    # Constraint 3: Only allowed direct flights may be taken.
    # Allowed direct flight pairs (bidirectional) based on the input:
    # (Geneva, Oslo), (Geneva, Paris), (Geneva, Porto),
    # (Paris, Oslo), (Porto, Paris),
    # (Paris, Reykjavik), (Reykjavik, Oslo),
    # (Porto, Oslo)
    allowed_pairs = [
        (0, 2), (2, 0),  # Geneva <-> Oslo
        (0, 1), (1, 0),  # Geneva <-> Paris
        (0, 3), (3, 0),  # Geneva <-> Porto
        (1, 2), (2, 1),  # Paris <-> Oslo
        (1, 3), (3, 1),  # Porto <-> Paris
        (1, 4), (4, 1),  # Paris <-> Reykjavik
        (2, 4), (4, 2),  # Oslo <-> Reykjavik (via "Reykjavik and Oslo")
        (2, 3), (3, 2)   # Oslo <-> Porto (via "Porto and Oslo")
    ]
    for i in range(num_segments - 1):
        a = cities[i]
        b = cities[i+1]
        flight_options = []
        for (ca, cb) in allowed_pairs:
            flight_options.append(And(a == ca, b == cb))
        solver.add(Or(flight_options))

    # Constraint 4: Specific city visit requirements.
    # - Geneva for 7 days: Already enforced by city 0 == Geneva and seg_duration = 7.
    # - Paris for 6 days, Porto for 7 days, Reykjavik for 2 days, Oslo for 5 days are fixed by the mapping.
    # - Oslo visit must include a day between day 19 and day 23 (to visit relatives).
    for i in range(num_segments):
        # If this segment is Oslo (2), then its interval [s[i], e[i]] must overlap with [19, 23].
        # This is satisfied if s[i] <= 23 and e[i] >= 19.
        solver.add(Implies(cities[i] == 2, And(s[i] <= 23, e[i] >= 19)))

    # Conference constraint: On day 1 and day 7, you attend a conference in Geneva.
    # Since the trip starts in Geneva (segment 0 spans Day 1-7), this is automatically satisfied.

    # Check and solve the constraints.
    if solver.check() == sat:
        model = solver.model()
        itinerary_output = []
        city_names = {0: "Geneva", 1: "Paris", 2: "Oslo", 3: "Porto", 4: "Reykjavik"}
        for i in range(num_segments):
            start_day = model.evaluate(s[i]).as_long()
            end_day = model.evaluate(e[i]).as_long()
            city_val = model.evaluate(cities[i]).as_long()
            itinerary_output.append({
                "day_range": f"Day {start_day}-{end_day}",
                "place": city_names[city_val]
            })
        result = {"itinerary": itinerary_output}
    else:
        result = {"itinerary": []}

    print(json.dumps(result))

if __name__ == "__main__":
    main()