import json
from constraint import Problem, AllDifferentConstraint

def main():
    # Define cities and required durations
    cities = [
        "Oslo",
        "Reykjavik",
        "Stockholm",
        "Munich",
        "Frankfurt",
        "Barcelona",
        "Bucharest",
        "Split",
    ]
    durations = {
        "Oslo": 2,
        "Reykjavik": 5,
        "Stockholm": 4,
        "Munich": 4,
        "Frankfurt": 4,
        "Barcelona": 3,
        "Bucharest": 2,
        "Split": 3,
    }

    # Direct flights (treated as undirected)
    direct_pairs = [
        ("Reykjavik", "Munich"),
        ("Munich", "Frankfurt"),
        ("Split", "Oslo"),
        ("Reykjavik", "Oslo"),
        ("Bucharest", "Munich"),
        ("Oslo", "Frankfurt"),
        ("Bucharest", "Barcelona"),
        ("Barcelona", "Frankfurt"),
        ("Reykjavik", "Frankfurt"),
        ("Barcelona", "Stockholm"),
        ("Barcelona", "Reykjavik"),
        ("Stockholm", "Reykjavik"),
        ("Barcelona", "Split"),
        ("Bucharest", "Oslo"),
        ("Bucharest", "Frankfurt"),
        ("Split", "Stockholm"),
        ("Barcelona", "Oslo"),
        ("Stockholm", "Munich"),
        ("Stockholm", "Oslo"),
        ("Split", "Frankfurt"),
        ("Barcelona", "Munich"),
        ("Stockholm", "Frankfurt"),
        ("Munich", "Oslo"),
        ("Split", "Munich"),
    ]
    flight_edges = set()
    for a, b in direct_pairs:
        flight_edges.add((a, b))
        flight_edges.add((b, a))

    # Create CSP
    problem = Problem()

    # Position variables for the 8 segments in order
    pos_vars = [f"P{i}" for i in range(1, 9)]
    start_vars = [f"S{i}" for i in range(1, 9)]
    end_vars = [f"E{i}" for i in range(1, 9)]

    # Add variables
    for v in pos_vars:
        problem.addVariable(v, cities)
    # All cities must be visited exactly once
    problem.addConstraint(AllDifferentConstraint(), pos_vars)

    # Day domains
    for s in start_vars:
        problem.addVariable(s, range(1, 21))
    for e in end_vars:
        problem.addVariable(e, range(1, 21))

    # Start at day 1 and end at day 20
    problem.addConstraint(lambda s1: s1 == 1, ("S1",))
    problem.addConstraint(lambda e8: e8 == 20, ("E8",))

    # Duration constraints for each segment
    for i in range(8):
        Pi, Si, Ei = pos_vars[i], start_vars[i], end_vars[i]
        def dur_constraint(city, s, e, durations=durations):
            return e - s + 1 == durations[city]
        problem.addConstraint(dur_constraint, (Pi, Si, Ei))

    # Consecutive day linking: S_{i+1} == E_i
    for i in range(7):
        Ei = end_vars[i]
        Sip1 = start_vars[i+1]
        problem.addConstraint(lambda e, s: s == e, (Ei, Sip1))

    # Direct flight constraints between consecutive cities
    for i in range(7):
        Pi, Pnext = pos_vars[i], pos_vars[i+1]
        def flight_constraint(c1, c2, flight_edges=flight_edges):
            return (c1, c2) in flight_edges
        problem.addConstraint(flight_constraint, (Pi, Pnext))

    # City-specific time window constraints
    # Oslo: exactly days 16-17
    for i in range(8):
        Pi, Si, Ei = pos_vars[i], start_vars[i], end_vars[i]
        def oslo_window(city, s, e):
            return True if city != "Oslo" else (s == 16 and e == 17)
        problem.addConstraint(oslo_window, (Pi, Si, Ei))

    # Frankfurt: must be 17-20 (4 days within 17-20 inclusive)
    for i in range(8):
        Pi, Si, Ei = pos_vars[i], start_vars[i], end_vars[i]
        def fra_window(city, s, e):
            return True if city != "Frankfurt" else (s == 17 and e == 20)
        problem.addConstraint(fra_window, (Pi, Si, Ei))

    # Reykjavik: 5 days, must intersect [9,13]
    for i in range(8):
        Pi, Si, Ei = pos_vars[i], start_vars[i], end_vars[i]
        def rkv_window(city, s, e):
            if city != "Reykjavik":
                return True
            # intersection with [9,13]
            return not (e < 9 or s > 13)
        problem.addConstraint(rkv_window, (Pi, Si, Ei))

    # Munich: 4 days, must intersect [13,16]
    for i in range(8):
        Pi, Si, Ei = pos_vars[i], start_vars[i], end_vars[i]
        def muc_window(city, s, e):
            if city != "Munich":
                return True
            return not (e < 13 or s > 16)
        problem.addConstraint(muc_window, (Pi, Si, Ei))

    # Solve
    solution = problem.getSolution()
    if not solution:
        raise RuntimeError("No feasible itinerary found under given constraints.")

    # Build itinerary in order
    itinerary = []
    for i in range(1, 9):
        city = solution[f"P{i}"]
        s = solution[f"S{i}"]
        e = solution[f"E{i}"]
        itinerary.append({
            "day_range": f"Day {s}-{e}",
            "place": city
        })

    print(json.dumps({"itinerary": itinerary}))

if __name__ == "__main__":
    main()