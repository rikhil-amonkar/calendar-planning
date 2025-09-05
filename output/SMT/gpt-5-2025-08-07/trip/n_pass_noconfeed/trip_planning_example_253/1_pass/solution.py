import json
from z3 import *

def main():
    # Input variables (trip constraints)
    total_days = 14
    cities = ["Amsterdam", "Vienna", "Santorini", "Lyon"]
    city_to_idx = {c: i for i, c in enumerate(cities)}
    idx_to_city = {i: c for c, i in city_to_idx.items()}

    # Desired presence days in each city
    target_days = {
        "Amsterdam": 3,
        "Vienna": 7,
        "Santorini": 4,
        "Lyon": 3
    }

    # Direct flight connections (undirected)
    direct_flights = {
        ("Vienna", "Lyon"),
        ("Vienna", "Santorini"),
        ("Vienna", "Amsterdam"),
        ("Amsterdam", "Santorini"),
        ("Lyon", "Amsterdam")
    }
    # Create oriented edge pairs including equality (stay)
    oriented_edges = set()
    n = len(cities)
    for i in range(n):
        oriented_edges.add((i, i))  # staying in the same city is allowed
    for a, b in direct_flights:
        i, j = city_to_idx[a], city_to_idx[b]
        oriented_edges.add((i, j))
        oriented_edges.add((j, i))

    # Create Z3 solver
    s = Solver()

    # Variables
    # city[d] is the base city (where you stay) on day d (1-based indexing for readability)
    city = [None] + [Int(f"city_{d}") for d in range(1, total_days + 1)]

    # presence[c][d] is True if city c is counted as present on day d
    presence = [[None] + [Bool(f"present_{c}_{d}") for d in range(1, total_days + 1)] for c in range(n)]

    # Domain constraints for city variables
    for d in range(1, total_days + 1):
        s.add(And(city[d] >= 0, city[d] < n))

    # Presence definition
    # If one flies from city A to city B on day d, then they are in both A and B on day d.
    for c in range(n):
        # Day 1: present iff base city is c
        s.add(presence[c][1] == (city[1] == c))
        for d in range(2, total_days + 1):
            s.add(
                presence[c][d] ==
                Or(
                    city[d] == c,
                    And(city[d - 1] == c, city[d] != city[d - 1])
                )
            )

    # Only direct flights between consecutive days (or stay in the same city)
    for d in range(2, total_days + 1):
        # The pair (city[d-1], city[d]) must be in oriented_edges
        allowed_pairs = [And(city[d - 1] == i, city[d] == j) for (i, j) in oriented_edges]
        s.add(Or(allowed_pairs))

    # Desired total presence days per city
    for cname, target in target_days.items():
        c = city_to_idx[cname]
        s.add(Sum([If(presence[c][d], 1, 0) for d in range(1, total_days + 1)]) == target)

    # Event constraints
    # Workshop in Amsterdam between day 9 and day 11 (inclusive)
    ams = city_to_idx["Amsterdam"]
    s.add(Or(presence[ams][9], presence[ams][10], presence[ams][11]))

    # Wedding in Lyon between day 7 and day 9 (inclusive)
    lyon = city_to_idx["Lyon"]
    s.add(Or(presence[lyon][7], presence[lyon][8], presence[lyon][9]))

    # Solve
    if s.check() != sat:
        print(json.dumps({"error": "No feasible itinerary found"}))
        return

    m = s.model()

    # Build itinerary as contiguous segments of the same base city
    base_cities = [None] + [m.evaluate(city[d]).as_long() for d in range(1, total_days + 1)]

    itinerary = []
    start = 1
    current = base_cities[1]
    for d in range(2, total_days + 1):
        if base_cities[d] != current:
            itinerary.append({
                "day_range": f"Day {start}-{d-1}",
                "place": idx_to_city[current]
            })
            start = d
            current = base_cities[d]
    # Add final segment
    itinerary.append({
        "day_range": f"Day {start}-{total_days}",
        "place": idx_to_city[current]
    })

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()