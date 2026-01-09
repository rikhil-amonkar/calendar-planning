import json
from constraint import Problem, AllDifferentConstraint

def main():
    # Cities and required durations (in days)
    cities = [
        "Prague", "Warsaw", "Dublin", "Athens", "Vilnius",
        "Porto", "London", "Seville", "Lisbon", "Dubrovnik"
    ]
    durations = {
        "Prague": 3,
        "Warsaw": 4,
        "Dublin": 3,
        "Athens": 3,
        "Vilnius": 4,
        "Porto": 5,
        "London": 3,
        "Seville": 2,
        "Lisbon": 5,
        "Dubrovnik": 3
    }
    total_days = 26

    # Direct flights as undirected edges
    direct_pairs = [
        ("Warsaw", "Vilnius"),
        ("Prague", "Athens"),
        ("London", "Lisbon"),
        ("Lisbon", "Porto"),
        ("Prague", "Lisbon"),
        ("London", "Dublin"),
        ("Athens", "Vilnius"),
        ("Athens", "Dublin"),
        ("Prague", "London"),
        ("London", "Warsaw"),
        ("Dublin", "Seville"),
        ("Seville", "Porto"),
        ("Lisbon", "Athens"),
        ("Dublin", "Porto"),
        ("Athens", "Warsaw"),
        ("Lisbon", "Warsaw"),
        ("Porto", "Warsaw"),
        ("Prague", "Warsaw"),
        ("Prague", "Dublin"),
        ("Athens", "Dubrovnik"),
        ("Lisbon", "Dublin"),
        ("Dubrovnik", "Dublin"),
        ("Lisbon", "Seville"),
        ("London", "Athens"),
    ]
    flights = {frozenset(p) for p in direct_pairs}

    # Problem setup
    problem = Problem()

    # Variables: start day for each city and position order in the chain 1..10
    # Start day domain ensures city fits within total_days
    for city in cities:
        problem.addVariable(f"S_{city}", range(1, total_days - durations[city] + 2))
        problem.addVariable(f"P_{city}", range(1, len(cities) + 1))

    # All positions must be different (a single Hamiltonian path ordering)
    problem.addConstraint(AllDifferentConstraint(), [f"P_{c}" for c in cities])

    # Helper to add pairwise sequencing and non-overlap constraints
    def pair_constraint_factory(city_a, city_b):
        da = durations[city_a]
        db = durations[city_b]
        def _constraint(pos_a, pos_b, s_a, s_b):
            e_a = s_a + da - 1
            e_b = s_b + db - 1
            # Adjacent in the sequence: must be directly connected and share boundary day
            if pos_b - pos_a == 1:
                if frozenset((city_a, city_b)) not in flights:
                    return False
                return e_a == s_b
            elif pos_a - pos_b == 1:
                if frozenset((city_a, city_b)) not in flights:
                    return False
                return e_b == s_a
            else:
                # Non-neighbors must not overlap (no touching to avoid extra overlaps)
                return e_a < s_b or e_b < s_a
        return _constraint

    # Apply pairwise constraints for all city pairs
    for i in range(len(cities)):
        for j in range(i + 1, len(cities)):
            a = cities[i]
            b = cities[j]
            problem.addConstraint(
                pair_constraint_factory(a, b),
                (f"P_{a}", f"P_{b}", f"S_{a}", f"S_{b}")
            )

    # Window constraints (cover required event windows)
    # "City must cover inclusive window [w_start, w_end]"
    def window_constraint_factory(city, w_start, w_end):
        d = durations[city]
        def _constraint(s):
            e = s + d - 1
            return s <= w_start and e >= w_end
        return _constraint

    # Prague workshop between day 1 and day 3 (and Prague for 3 days)
    problem.addConstraint(window_constraint_factory("Prague", 1, 3), [f"S_Prague"])
    # London wedding between day 3 and day 5
    problem.addConstraint(window_constraint_factory("London", 3, 5), [f"S_London"])
    # Lisbon relatives between day 5 and day 9
    problem.addConstraint(window_constraint_factory("Lisbon", 5, 9), [f"S_Lisbon"])
    # Porto conference during day 16 and day 20
    problem.addConstraint(window_constraint_factory("Porto", 16, 20), [f"S_Porto"])
    # Warsaw friends between day 20 and day 23
    problem.addConstraint(window_constraint_factory("Warsaw", 20, 23), [f"S_Warsaw"])

    # Fix positions to reduce symmetry and align with windows-derived sequence:
    # Start the chain at Prague and end at Vilnius, with Porto before Warsaw, etc.
    problem.addConstraint(lambda p: p == 1, [f"P_Prague"])
    problem.addConstraint(lambda p: p == 2, [f"P_London"])
    problem.addConstraint(lambda p: p == 3, [f"P_Lisbon"])
    problem.addConstraint(lambda p: p == 8, [f"P_Porto"])
    problem.addConstraint(lambda p: p == 9, [f"P_Warsaw"])
    problem.addConstraint(lambda p: p == 10, [f"P_Vilnius"])

    # Solve
    solution = problem.getSolution()

    if not solution:
        print(json.dumps({"error": "No feasible itinerary found with given constraints."}))
        return

    # Build itinerary sorted by start day
    segments = []
    for city in cities:
        s = solution[f"S_{city}"]
        e = s + durations[city] - 1
        segments.append((s, e, city))

    segments.sort(key=lambda x: x[0])

    itinerary = []
    for s, e, city in segments:
        itinerary.append({
            "day_range": f"Day {s}-{e}",
            "place": city
        })

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()