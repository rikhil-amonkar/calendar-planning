import json
from constraint import Problem

def main():
    # Define problem parameters
    total_days = 16
    cities = ["Frankfurt", "Manchester", "Valencia", "Naples", "Oslo", "Vilnius"]

    # Desired days in each city (counting flight days for both cities)
    desired_days = {
        "Frankfurt": 4,
        "Manchester": 4,
        "Valencia": 4,
        "Naples": 4,
        "Oslo": 3,
        "Vilnius": 2,
    }

    # Direct flight pairs (undirected)
    direct_pairs = [
        ("Valencia", "Frankfurt"),
        ("Manchester", "Frankfurt"),
        ("Naples", "Manchester"),
        ("Naples", "Frankfurt"),
        ("Naples", "Oslo"),
        ("Oslo", "Frankfurt"),
        ("Vilnius", "Frankfurt"),
        ("Oslo", "Vilnius"),
        ("Manchester", "Oslo"),
        ("Valencia", "Naples"),
    ]
    direct_edges = set(frozenset(p) for p in direct_pairs)

    # Initialize constraint problem
    problem = Problem()

    # Create variables Day1..Day16 with domains
    # Fix Day12 = Vilnius for the wedding, Days 13-16 = Frankfurt for the show
    # Other days can be any city, but to satisfy exact desired counts, Frankfurt cannot appear before Day13
    for d in range(1, total_days + 1):
        var = f"Day{d}"
        if d == 12:
            problem.addVariable(var, ["Vilnius"])
        elif d in (13, 14, 15, 16):
            problem.addVariable(var, ["Frankfurt"])
        else:
            # Exclude Frankfurt from early days to respect the 4-day total exactly (allocated to Days 13-16)
            problem.addVariable(var, [c for c in cities if c != "Frankfurt"])

    # Adjacency constraint: consecutive days must be same city or a direct flight
    def adjacent_or_same(a, b):
        return a == b or frozenset({a, b}) in direct_edges

    for d in range(2, total_days + 1):
        problem.addConstraint(adjacent_or_same, (f"Day{d-1}", f"Day{d}"))

    # Global count constraint: ensure total days per city (including flight-day double counting) match desired_days exactly
    def counts_match(*vals):
        # vals are ordered by Day1..Day16
        day_to_city = {i + 1: vals[i] for i in range(len(vals))}

        counts = {c: 0 for c in cities}
        # Count presence per rule:
        # - On each day d, you're in city Day[d]
        # - If Day[d-1] != Day[d], then on day d you're also in Day[d-1]
        for d in range(1, total_days + 1):
            curr = day_to_city[d]
            counts[curr] += 1
            if d > 1:
                prev = day_to_city[d - 1]
                if prev != curr:
                    counts[prev] += 1

        # Must match desired exactly
        for c in cities:
            if counts[c] != desired_days[c]:
                return False
        return True

    problem.addConstraint(
        counts_match,
        tuple([f"Day{d}" for d in range(1, total_days + 1)])
    )

    # Find a solution
    solution = problem.getSolution()

    if not solution:
        # Fallback: output empty itinerary if no solution found
        print(json.dumps({"itinerary": []}))
        return

    # Build itinerary ranges
    # Sort days
    days_sorted = [solution[f"Day{d}"] for d in range(1, total_days + 1)]

    itinerary = []
    start = 1
    curr_city = days_sorted[0]

    for d in range(2, total_days + 1):
        city = days_sorted[d - 1]
        if city != curr_city:
            itinerary.append({
                "day_range": f"Day {start}-{d - 1}",
                "place": curr_city
            })
            start = d
            curr_city = city
    # Append last segment
    itinerary.append({
        "day_range": f"Day {start}-{total_days}",
        "place": curr_city
    })

    print(json.dumps({"itinerary": itinerary}))

if __name__ == "__main__":
    main()