import json
from constraint import Problem, AllDifferentConstraint

def main():
    # Input data
    cities = ["Mykonos", "Nice", "Zurich", "Prague", "Valencia", "Riga", "Bucharest"]
    total_days = 22

    # Required stays (days count in each city, inclusive of travel day overlaps)
    lengths = {
        "Valencia": 5,
        "Riga": 5,
        "Prague": 3,
        "Mykonos": 3,
        "Zurich": 5,
        "Bucharest": 5,
        "Nice": 2,
    }

    # Direct flight pairs (undirected)
    direct_pairs = [
        ("Mykonos", "Nice"),
        ("Mykonos", "Zurich"),
        ("Prague", "Bucharest"),
        ("Valencia", "Bucharest"),
        ("Zurich", "Prague"),
        ("Riga", "Nice"),
        ("Zurich", "Riga"),
        ("Zurich", "Bucharest"),
        ("Zurich", "Valencia"),
        ("Bucharest", "Riga"),
        ("Prague", "Riga"),
        ("Prague", "Valencia"),
        ("Zurich", "Nice"),
    ]
    direct_edges = set(frozenset([a, b]) for a, b in direct_pairs)

    # Special time window constraints (inclusive)
    # Attending a wedding in Mykonos between day 1 and day 3 (must be in Mykonos on days 1,2,3)
    wedding_city = "Mykonos"
    wedding_start, wedding_end = 1, 3

    # Visiting relatives in Prague between day 7 and 9 (must be in Prague on 7,8,9)
    relatives_city = "Prague"
    relatives_start, relatives_end = 7, 9

    # Decision variables: ordered path of 7 distinct cities
    positions = [f"pos{i}" for i in range(1, 8)]
    problem = Problem()
    for p in positions:
        problem.addVariable(p, cities)
    problem.addConstraint(AllDifferentConstraint(), positions)

    # Helper to compute start and end days of each position given the order
    def compute_starts(order):
        starts = [1] * len(order)
        for i in range(1, len(order)):
            prev_city = order[i - 1]
            starts[i] = starts[i - 1] + lengths[prev_city] - 1  # overlap travel day
        ends = [starts[i] + lengths[order[i]] - 1 for i in range(len(order))]
        return starts, ends

    # Adjacency (direct flight) constraints between consecutive positions
    def adjacent_direct(a, b):
        return frozenset([a, b]) in direct_edges

    for i in range(1, 7):
        problem.addConstraint(adjacent_direct, (f"pos{i}", f"pos{i+1}"))

    # Mykonos must include days 1..3; since start day must be 1 for a 3-day block,
    # this effectively places Mykonos at position 1
    # Enforce directly to reduce search space and satisfy the event.
    problem.addConstraint(lambda c: c == wedding_city, ("pos1",))

    # Time window constraints:
    # - Prague must include days 7..9
    # - Mykonos must include days 1..3 (redundant due to pos1 fix, but we keep as a semantic check)
    def time_windows(*order_values):
        order = list(order_values)
        starts, ends = compute_starts(order)

        # Build city -> (start, end) map
        city_to_range = {order[i]: (starts[i], ends[i]) for i in range(len(order))}

        # Mykonos window
        m_s, m_e = city_to_range[wedding_city]
        if not (m_s <= wedding_start and m_e >= wedding_end):
            return False

        # Prague window
        p_s, p_e = city_to_range[relatives_city]
        if not (p_s <= relatives_start and p_e >= relatives_end):
            return False

        # Validate last day equals total_days for union span
        # With overlaps, final end should be total_days if the chain is continuous.
        if ends[-1] != total_days:
            return False

        return True

    problem.addConstraint(time_windows, tuple(positions))

    # Solve
    solution = problem.getSolution()
    if solution is None:
        print(json.dumps({"itinerary": []}))
        return

    # Construct ordered list and compute day ranges
    order = [solution[f"pos{i}"] for i in range(1, 8)]
    starts, ends = compute_starts(order)

    itinerary = []
    for i, city in enumerate(order):
        itinerary.append({
            "day_range": f"Day {starts[i]}-{ends[i]}",
            "place": city
        })

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()