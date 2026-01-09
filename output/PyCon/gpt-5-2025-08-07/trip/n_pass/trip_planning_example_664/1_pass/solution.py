import json
from constraint import Problem, AllDifferentConstraint

def main():
    # Define cities and durations
    cities = ["Tallinn", "Bucharest", "Seville", "Stockholm", "Munich", "Milan"]
    durations = {
        "Tallinn": 2,
        "Bucharest": 4,
        "Seville": 5,
        "Stockholm": 5,
        "Munich": 5,
        "Milan": 2,
    }
    total_days = 18

    # Direct flights (undirected)
    direct_pairs = [
        ("Milan", "Stockholm"),
        ("Munich", "Stockholm"),
        ("Bucharest", "Munich"),
        ("Munich", "Seville"),
        ("Stockholm", "Tallinn"),
        ("Munich", "Milan"),
        ("Munich", "Tallinn"),
        ("Seville", "Milan"),
    ]
    direct_edges = set(frozenset(pair) for pair in direct_pairs)

    def has_direct(a, b):
        return frozenset((a, b)) in direct_edges

    def overlaps(a_start, a_end, b_start, b_end):
        return max(a_start, b_start) <= min(a_end, b_end)

    # Constraint problem
    problem = Problem()

    # Variables: order positions 0..5 each holds a city name
    positions = [f"pos{i}" for i in range(6)]
    for p in positions:
        problem.addVariable(p, cities)

    # All cities must be distinct
    problem.addConstraint(AllDifferentConstraint(), positions)

    # Master constraint: validates adjacency, timing, windows, and total days
    def itinerary_constraint(c0, c1, c2, c3, c4, c5):
        order = [c0, c1, c2, c3, c4, c5]

        # Direct flights between consecutive cities
        for i in range(5):
            if not has_direct(order[i], order[i+1]):
                return False

        # Compute start days with overlap on transition days
        starts = [0] * 6
        starts[0] = 1
        for i in range(1, 6):
            prev_city = order[i-1]
            starts[i] = starts[i-1] + durations[prev_city] - 1

        # Ensure the total trip length is exactly total_days
        last_city = order[5]
        last_end = starts[5] + durations[last_city] - 1
        if last_end != total_days:
            return False

        # Bucharest: must be days 1-4 exactly (stay 4 days and within days 1-4)
        if "Bucharest" not in order:
            return False
        b_idx = order.index("Bucharest")
        if not (starts[b_idx] == 1 and (starts[b_idx] + durations["Bucharest"] - 1) == 4):
            return False
        # Therefore, Bucharest must be first
        if b_idx != 0:
            return False

        # Munich: overlap with days 4-8 (wedding window)
        if "Munich" not in order:
            return False
        m_idx = order.index("Munich")
        m_start = starts[m_idx]
        m_end = m_start + durations["Munich"] - 1
        if not overlaps(m_start, m_end, 4, 8):
            return False

        # Seville: overlap with days 8-12 (friends window)
        if "Seville" not in order:
            return False
        s_idx = order.index("Seville")
        s_start = starts[s_idx]
        s_end = s_start + durations["Seville"] - 1
        if not overlaps(s_start, s_end, 8, 12):
            return False

        return True

    problem.addConstraint(
        itinerary_constraint,
        positions
    )

    solutions = problem.getSolutions()

    # Pick the first valid solution and compute the itinerary
    if not solutions:
        result = {"itinerary": []}
    else:
        sol = solutions[0]
        order = [sol[f"pos{i}"] for i in range(6)]
        # Compute starts and ends
        starts = [0] * 6
        starts[0] = 1
        for i in range(1, 6):
            prev_city = order[i - 1]
            starts[i] = starts[i - 1] + durations[prev_city] - 1
        itinerary = []
        for i, city in enumerate(order):
            start_day = starts[i]
            end_day = start_day + durations[city] - 1
            itinerary.append({
                "day_range": f"Day {start_day}-{end_day}",
                "place": city
            })
        result = {"itinerary": itinerary}

    print(json.dumps(result, ensure_ascii=False))

if __name__ == "__main__":
    main()