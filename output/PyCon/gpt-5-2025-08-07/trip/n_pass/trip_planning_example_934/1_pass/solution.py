import json
from constraint import Problem, AllDifferentConstraint

def main():
    # Define cities and required stay durations (in days)
    cities = [
        "Brussels",
        "Rome",
        "Dubrovnik",
        "Geneva",
        "Budapest",
        "Riga",
        "Valencia",
    ]
    durations = {
        "Brussels": 5,
        "Rome": 2,
        "Dubrovnik": 3,
        "Geneva": 5,
        "Budapest": 2,
        "Riga": 4,
        "Valencia": 2,
    }

    # Build directed flight network (only direct flights allowed)
    edges = set()
    def add_bidirectional(a, b):
        edges.add((a, b))
        edges.add((b, a))

    # "and" means bidirectional
    add_bidirectional("Brussels", "Valencia")
    add_bidirectional("Rome", "Valencia")
    add_bidirectional("Brussels", "Geneva")
    add_bidirectional("Rome", "Geneva")
    add_bidirectional("Dubrovnik", "Geneva")
    add_bidirectional("Valencia", "Geneva")
    add_bidirectional("Geneva", "Budapest")
    add_bidirectional("Riga", "Brussels")
    add_bidirectional("Rome", "Budapest")
    add_bidirectional("Rome", "Brussels")
    add_bidirectional("Brussels", "Budapest")
    add_bidirectional("Dubrovnik", "Rome")
    # Directed flight
    edges.add(("Rome", "Riga"))

    # Helper to check interval intersection
    def intersects(a_start, a_end, b_start, b_end):
        return not (a_end < b_start or a_start > b_end)

    # Create CSP
    problem = Problem()

    # Variables for city order
    city_vars = [f"City_{i}" for i in range(1, 8)]
    for v in city_vars:
        problem.addVariable(v, cities)
    problem.addConstraint(AllDifferentConstraint(), city_vars)

    # Variables for start days (S1..S7)
    start_vars = [f"S_{i}" for i in range(1, 8)]
    problem.addVariable(start_vars[0], [1])  # trip starts on Day 1
    for v in start_vars[1:]:
        problem.addVariable(v, list(range(1, 18)))

    # Recurrence constraints for contiguous stays with overlap on travel day
    # S_{i+1} = S_i + duration(City_i) - 1
    for i in range(1, 7):
        ci = f"City_{i}"
        si = f"S_{i}"
        si1 = f"S_{i+1}"
        def recur_constraint(city_i, s_i, s_i1, durations=durations):
            return s_i1 == s_i + durations[city_i] - 1
        problem.addConstraint(recur_constraint, (ci, si, si1))

    # Direct flight constraints between consecutive cities
    for i in range(1, 7):
        ci = f"City_{i}"
        ci1 = f"City_{i+1}"
        def flight_constraint(city_a, city_b, edges=edges):
            return (city_a, city_b) in edges
        problem.addConstraint(flight_constraint, (ci, ci1))

    # Window constraints:
    # - Brussels: at least one day between day 7 and 11
    # - Budapest: meet friend between day 16 and 17
    # - Riga: meet friends between day 4 and 7
    for i in range(1, 8):
        ci = f"City_{i}"
        si = f"S_{i}"

        def brussels_window(city, s, durations=durations):
            if city != "Brussels":
                return True
            start = s
            end = s + durations["Brussels"] - 1
            return intersects(start, end, 7, 11)
        problem.addConstraint(brussels_window, (ci, si))

        def budapest_window(city, s, durations=durations):
            if city != "Budapest":
                return True
            start = s
            end = s + durations["Budapest"] - 1
            return intersects(start, end, 16, 17)
        problem.addConstraint(budapest_window, (ci, si))

        def riga_window(city, s, durations=durations):
            if city != "Riga":
                return True
            start = s
            end = s + durations["Riga"] - 1
            return intersects(start, end, 4, 7)
        problem.addConstraint(riga_window, (ci, si))

    # Solve (find one feasible itinerary)
    solution = problem.getSolution()

    if not solution:
        print(json.dumps({"error": "No feasible itinerary found with given constraints."}))
        return

    # Build itinerary output
    itinerary = []
    for i in range(1, 8):
        city = solution[f"City_{i}"]
        s = solution[f"S_{i}"]
        e = s + durations[city] - 1
        itinerary.append({
            "day_range": f"Day {s}-{e}",
            "place": city
        })

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()