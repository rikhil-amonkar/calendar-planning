import json
from z3 import *

def main():
    # Define cities
    cities = ["Stuttgart", "Bucharest", "Geneva", "Valencia", "Munich"]
    STUTTGART, BUCHAREST, GENEVA, VALENCIA, MUNICH = range(5)

    # Required stay durations per city
    required_days = {
        STUTTGART: 2,
        BUCHAREST: 2,
        GENEVA: 4,
        VALENCIA: 6,
        MUNICH: 7,
    }

    total_trip_days = 17
    num_segments = 5  # We will visit each city once, giving 4 flights (overlap days)

    # Direct flight edges (undirected)
    edges = set()
    def add_edge(a, b):
        edges.add((a, b))
        edges.add((b, a))

    add_edge(GENEVA, MUNICH)
    add_edge(MUNICH, VALENCIA)
    add_edge(BUCHAREST, VALENCIA)
    add_edge(MUNICH, BUCHAREST)
    add_edge(VALENCIA, STUTTGART)
    add_edge(GENEVA, VALENCIA)

    # Z3 variables
    pos = [Int(f"pos_{i}") for i in range(num_segments)]        # city at segment i
    start = [Int(f"start_{i}") for i in range(num_segments)]    # start day (inclusive)
    end = [Int(f"end_{i}") for i in range(num_segments)]        # end day (inclusive)
    dur = [Int(f"dur_{i}") for i in range(num_segments)]        # duration for segment i

    s = Solver()

    # Domains and base constraints
    for i in range(num_segments):
        s.add(pos[i] >= 0, pos[i] <= 4)
        s.add(start[i] >= 1, start[i] <= total_trip_days)
        s.add(end[i] >= 1, end[i] <= total_trip_days)
        s.add(dur[i] == end[i] - start[i] + 1)
        # duration must match the required duration of the city assigned to this segment
        s.add(dur[i] == Sum([If(pos[i] == c, required_days[c], 0) for c in range(5)]))

    # Each city is visited exactly once
    s.add(Distinct(*pos))

    # Timeline chaining with overlap on flight days
    s.add(start[0] == 1)
    for i in range(1, num_segments):
        s.add(start[i] == end[i-1])  # flying on the boundary day: both cities share that day

    s.add(end[num_segments - 1] == total_trip_days)

    # Direct flight constraints between consecutive segments
    def edge_allowed(u, v):
        return Or([And(u == IntVal(a), v == IntVal(b)) for (a, b) in edges])

    for i in range(1, num_segments):
        s.add(edge_allowed(pos[i-1], pos[i]))

    # Window constraints:
    # - Visit relatives in Geneva between day 1 and day 4 (at least one day overlap)
    s.add(Or([And(pos[i] == GENEVA, start[i] <= 4, end[i] >= 1) for i in range(num_segments)]))
    # - Meet friends in Munich between day 4 and day 10 (at least one day overlap)
    s.add(Or([And(pos[i] == MUNICH, start[i] <= 10, end[i] >= 4) for i in range(num_segments)]))

    # Solve
    if s.check() != sat:
        print(json.dumps({"itinerary": [], "error": "No feasible itinerary found"}))
        return

    m = s.model()

    # Build itinerary output
    itinerary = []
    for i in range(num_segments):
        city_idx = m[pos[i]].as_long()
        s_day = m[start[i]].as_long()
        e_day = m[end[i]].as_long()
        itinerary.append({
            "day_range": f"Day {s_day}-{e_day}",
            "place": cities[city_idx]
        })

    print(json.dumps({"itinerary": itinerary}))

if __name__ == "__main__":
    main()