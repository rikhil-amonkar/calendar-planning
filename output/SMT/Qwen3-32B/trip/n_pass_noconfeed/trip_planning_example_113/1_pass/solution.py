from z3 import *
import json

def main():
    solver = Solver()

    # Define cities as integers: 0=Naples, 1=Seville, 2=Milan
    city0 = Int('city0')
    city1 = Int('city1')
    city2 = Int('city2')

    # Constraints for cities
    solver.add(Distinct(city0, city1, city2))
    solver.add(city2 == 1)  # Third segment must be Seville

    # Allowed transitions between cities
    def is_allowed_transition(prev, curr):
        return Or(
            And(prev == 0, curr == 2),  # Naples -> Milan
            And(prev == 2, curr == 0),  # Milan -> Naples
            And(prev == 2, curr == 1),  # Milan -> Seville
            And(prev == 1, curr == 2)   # Seville -> Milan
        )

    solver.add(is_allowed_transition(city0, city1))
    solver.add(is_allowed_transition(city1, city2))

    # Compute durations based on city
    d0 = If(city0 == 0, 3, If(city0 == 1, 4, 7))
    d1 = If(city1 == 0, 3, If(city1 == 1, 4, 7))
    d2 = 4  # Seville's duration is fixed

    # Compute end days
    e0 = 1 + d0 - 1
    s1 = e0
    e1 = s1 + d1 - 1
    s2 = e1
    e2 = s2 + d2 - 1

    # The last day must be 12
    solver.add(e2 == 12)

    if solver.check() == sat:
        model = solver.model()
        c0 = model[city0].as_long()
        c1 = model[city1].as_long()
        c2 = model[city2].as_long()

        # Compute durations for each segment
        durations = [
            3 if c == 0 else 7 if c == 2 else 4 for c in [c0, c1, c2]
        ]

        # Compute start and end days for each segment
        segments = []
        start = 1
        for dur in durations:
            end = start + dur - 1
            segments.append((start, end))
            start = end

        # Prepare the itinerary
        city_names = {0: "Naples", 1: "Seville", 2: "Milan"}
        itinerary = []
        for (s, e), c in zip(segments, [c0, c1, c2]):
            day_range = f"Day {s}-{e}"
            itinerary.append({"day_range": day_range, "place": city_names[c]})

        print(json.dumps({"itinerary": itinerary}))
    else:
        print(json.dumps({"error": "No solution found"}))

if __name__ == "__main__":
    main()