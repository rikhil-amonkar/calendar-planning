import json
from constraint import Problem, AllDifferentConstraint

def main():
    # Define cities and durations (inclusive of flight day counted in both cities)
    cities = ["Krakow", "Frankfurt", "Oslo", "Dubrovnik", "Naples"]
    durations = {
        "Krakow": 5,
        "Frankfurt": 4,
        "Oslo": 3,
        "Dubrovnik": 5,
        "Naples": 5,
    }

    # Direct flight connections (undirected)
    direct_pairs = [
        ("Dubrovnik", "Oslo"),
        ("Frankfurt", "Krakow"),
        ("Frankfurt", "Oslo"),
        ("Dubrovnik", "Frankfurt"),
        ("Krakow", "Oslo"),
        ("Naples", "Oslo"),
        ("Naples", "Dubrovnik"),
        ("Naples", "Frankfurt"),
    ]
    direct_edges = {frozenset(p) for p in direct_pairs}

    # Total trip days and windows
    total_days = 18
    dubrovnik_window = (5, 9)   # inclusive
    oslo_window = (16, 18)      # inclusive

    # Set up CSP
    problem = Problem()

    # Variables: city order (5 segments) and start days s0..s4
    city_vars = [f"City{i}" for i in range(5)]
    start_vars = [f"s{i}" for i in range(5)]

    for v in city_vars:
        problem.addVariable(v, cities)
    for v in start_vars:
        problem.addVariable(v, range(1, total_days + 1))

    # Each city exactly once
    problem.addConstraint(AllDifferentConstraint(), tuple(city_vars))

    # Start on Day 1
    problem.addConstraint(lambda s0: s0 == 1, ("s0",))

    # Recurrence for contiguous segments with flight day counted in both cities:
    # s_{i+1} = s_i + duration(City_i) - 1
    def recurrence(s_i, s_next, city_i):
        return s_next == s_i + durations[city_i] - 1

    for i in range(4):
        problem.addConstraint(recurrence, (f"s{i}", f"s{i+1}", f"City{i}"))

    # Final end day must be Day 18 (this will be implied, but we enforce explicitly)
    def final_end_ok(s4, city4):
        return s4 + durations[city4] - 1 == total_days

    problem.addConstraint(final_end_ok, ("s4", "City4"))

    # Direct flight constraint between consecutive cities
    def flight_ok(city_i, city_next):
        return frozenset((city_i, city_next)) in direct_edges

    for i in range(4):
        problem.addConstraint(flight_ok, (f"City{i}", f"City{i+1}"))

    # Window overlap helper
    def interval_intersects(start, dur, window_start, window_end):
        end = start + dur - 1
        return not (end < window_start or start > window_end)

    # Dubrovnik window: must overlap [5,9]
    def dubrovnik_window_ok(city, s):
        if city != "Dubrovnik":
            return True
        return interval_intersects(s, durations[city], dubrovnik_window[0], dubrovnik_window[1])

    # Oslo window: must overlap [16,18]
    def oslo_window_ok(city, s):
        if city != "Oslo":
            return True
        return interval_intersects(s, durations[city], oslo_window[0], oslo_window[1])

    for i in range(5):
        problem.addConstraint(dubrovnik_window_ok, (f"City{i}", f"s{i}"))
        problem.addConstraint(oslo_window_ok, (f"City{i}", f"s{i}"))

    solutions = problem.getSolutions()

    # Select an "optimal" solution:
    # Minimize |Oslo start - 16| + |Dubrovnik midpoint - 7|
    # Dubrovnik midpoint (for 5 days) is s + 2
    def sol_key(sol):
        order = [sol[f"City{i}"] for i in range(5)]
        starts = [sol[f"s{i}"] for i in range(5)]
        pos_oslo = order.index("Oslo")
        pos_dub = order.index("Dubrovnik")
        s_oslo = starts[pos_oslo]
        s_dub = starts[pos_dub]
        cost = abs(s_oslo - 16) + abs((s_dub + 2) - 7)
        # Tiebreakers for determinism
        return (cost, tuple(order), tuple(starts))

    best = None
    if solutions:
        best = min(solutions, key=sol_key)

    itinerary = []
    if best:
        order = [best[f"City{i}"] for i in range(5)]
        starts = [best[f"s{i}"] for i in range(5)]
        for i in range(5):
            city = order[i]
            s = starts[i]
            e = s + durations[city] - 1
            itinerary.append({
                "day_range": f"Day {s}-{e}",
                "place": city
            })

    print(json.dumps({"itinerary": itinerary}))

if __name__ == "__main__":
    main()