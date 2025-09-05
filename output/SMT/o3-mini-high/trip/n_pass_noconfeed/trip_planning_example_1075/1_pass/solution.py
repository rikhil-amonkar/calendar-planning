import json
from z3 import *

def main():
    # Define the list of cities and their required durations.
    # City indices:
    # 0: Vienna (4 days)
    # 1: Lyon (3 days)
    # 2: Edinburgh (4 days) + must cover days 5-8 (annual show)
    # 3: Reykjavik (5 days)
    # 4: Stuttgart (5 days)
    # 5: Manchester (2 days)
    # 6: Split (5 days) + must cover at least one day between days 19-23 (wedding)
    # 7: Prague (4 days)
    cities = ["Vienna", "Lyon", "Edinburgh", "Reykjavik", "Stuttgart", "Manchester", "Split", "Prague"]
    duration_map = {0: 4, 1: 3, 2: 4, 3: 5, 4: 5, 5: 2, 6: 5, 7: 4}
    
    solver = Solver()
    num_segments = 8

    # For each segment, we define:
    #   itinerary[i]: the city visited (as an integer from 0 to 7 corresponding to cities list)
    #   s[i]: the starting day (inclusive) of the visit
    #   e[i]: the ending day (inclusive) of the visit
    itinerary = [Int(f"city_{i}") for i in range(num_segments)]
    s = [Int(f"s_{i}") for i in range(num_segments)]
    e = [Int(f"e_{i}") for i in range(num_segments)]

    # Each city must appear exactly once.
    for i in range(num_segments):
        solver.add(itinerary[i] >= 0, itinerary[i] < 8)
    solver.add(Distinct(itinerary))
    
    # s and e day numbers must lie within the overall trip (1 to 25), and each segment's start is before or equal its end.
    for i in range(num_segments):
        solver.add(s[i] >= 1, e[i] <= 25, s[i] <= e[i])
    
    # The trip starts on day 1 and ends on day 25.
    solver.add(s[0] == 1)
    solver.add(e[num_segments - 1] == 25)
    
    # Each segment i must last exactly the required number of days for that city.
    # Note: if a flight from city A to city B is taken on day X, then day X is counted in both visits.
    # Thus, for a segment with days s to e, we have e - s + 1 = (required days for that city).
    for i in range(num_segments):
        c = itinerary[i]
        duration_expr = If(c == 0, 4,
                         If(c == 1, 3,
                         If(c == 2, 4,
                         If(c == 3, 5,
                         If(c == 4, 5,
                         If(c == 5, 2,
                         If(c == 6, 5,
                         If(c == 7, 4, 0))))))))
        solver.add(e[i] - s[i] + 1 == duration_expr)
    
    # Flight transition: if you fly from a city A to city B on day X, then day X is in both A and B.
    # Therefore, the start day of segment i+1 equals the end day of segment i.
    for i in range(num_segments - 1):
        solver.add(s[i+1] == e[i])
    
    # Allowed direct flights (using city indices):
    # Note: Some flights are directional:
    # - From Reykjavik to Stuttgart only: (3, 4)
    # - From Manchester to Split only: (5, 6)
    # The others are bidirectional.
    allowed_edges = [
        (3, 4),               # Reykjavik -> Stuttgart (directional)
        (4, 6), (6, 4),       # Stuttgart and Split (bidirectional)
        (4, 0), (0, 4),       # Stuttgart and Vienna (bidirectional)
        (7, 5), (5, 7),       # Prague and Manchester (bidirectional)
        (2, 7), (7, 2),       # Edinburgh and Prague (bidirectional)
        (5, 6),               # Manchester -> Split (directional)
        (7, 0), (0, 7),       # Prague and Vienna (bidirectional)
        (0, 5), (5, 0),       # Vienna and Manchester (bidirectional)
        (7, 6), (6, 7),       # Prague and Split (bidirectional)
        (0, 1), (1, 0),       # Vienna and Lyon (bidirectional)
        (4, 2), (2, 4),       # Stuttgart and Edinburgh (bidirectional)
        (6, 1), (1, 6),       # Split and Lyon (bidirectional)
        (4, 5), (5, 4),       # Stuttgart and Manchester (bidirectional)
        (7, 1), (1, 7),       # Prague and Lyon (bidirectional)
        (3, 0), (0, 3),       # Reykjavik and Vienna (bidirectional)
        (7, 3), (3, 7),       # Prague and Reykjavik (bidirectional)
        (0, 6), (6, 0)        # Vienna and Split (bidirectional)
    ]
    for i in range(num_segments - 1):
        possible_transitions = []
        for (a, b) in allowed_edges:
            possible_transitions.append(And(itinerary[i] == a, itinerary[i+1] == b))
        solver.add(Or(possible_transitions))
    
    # Special event constraints:
    # Edinburgh (city index 2) must cover the annual show from day 5 to day 8.
    for i in range(num_segments):
        solver.add(Or(itinerary[i] != 2, And(s[i] <= 5, e[i] >= 8)))
    # Split (city index 6) must include at least one day between day 19 and day 23 for the wedding.
    for i in range(num_segments):
        solver.add(Or(itinerary[i] != 6, And(s[i] <= 23, e[i] >= 19)))
    
    if solver.check() == sat:
        m = solver.model()
        plan = []
        for i in range(num_segments):
            start_day = m[s[i]].as_long()
            end_day = m[e[i]].as_long()
            city_index = m[itinerary[i]].as_long()
            plan.append({
                "day_range": f"Day {start_day}-{end_day}",
                "place": cities[city_index]
            })
        output = {"itinerary": plan}
        print(json.dumps(output))
    else:
        print(json.dumps({"error": "No solution found"}))

if __name__ == "__main__":
    main()