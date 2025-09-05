import json
import itertools

def find_itinerary(total_days, city_durations, direct_flights, conference_requirements):
    # Build undirected adjacency set for quick lookup
    adjacency = {}
    for a, b in direct_flights:
        adjacency.setdefault(a, set()).add(b)
        adjacency.setdefault(b, set()).add(a)

    cities = list(city_durations.keys())
    required_last_day_city = conference_requirements.get(total_days, None)

    # Validate basic feasibility: sum of durations must equal total_days + (number_of_flights)
    # For a path visiting N cities, flights = N-1
    n_cities = len(cities)
    if sum(city_durations.values()) != total_days + (n_cities - 1):
        raise ValueError("Durations cannot fit into total days with allowed flight overlaps.")

    def is_path_with_direct_flights(order):
        for i in range(len(order) - 1):
            if order[i+1] not in adjacency.get(order[i], set()):
                return False
        return True

    solutions = []
    for order in itertools.permutations(cities):
        # Enforce that the last-day city (if specified) must be the last in the order
        if required_last_day_city and order[-1] != required_last_day_city:
            continue

        # Check direct flights between consecutive cities
        if not is_path_with_direct_flights(order):
            continue

        # Given order [C1, C2, C3], with inclusive overlap on flight days,
        # counts must satisfy:
        # C1_count = F1
        # C2_count = F2 - F1 + 1
        # C3_count = total_days - F2 + 1
        # So:
        # F1 = duration[C1]
        # F2 = F1 + duration[C2] - 1
        c1, c2, c3 = order
        F1 = city_durations[c1]
        F2 = F1 + city_durations[c2] - 1

        # Validate bounds
        if not (1 <= F1 < F2 <= total_days):
            continue

        # Validate third city's duration
        if (total_days - F2 + 1) != city_durations[c3]:
            continue

        # Validate conference requirements: day must be in the relevant city's occupied interval
        # City intervals (inclusive):
        # c1: [1, F1]
        # c2: [F1, F2]
        # c3: [F2, total_days]
        ok = True
        for day, city in conference_requirements.items():
            in_city = False
            if city == c1 and 1 <= day <= F1:
                in_city = True
            elif city == c2 and F1 <= day <= F2:
                in_city = True
            elif city == c3 and F2 <= day <= total_days:
                in_city = True
            if not in_city:
                ok = False
                break

        if not ok:
            continue

        # Build itinerary segments as day ranges:
        segments = [
            {"day_range": f"Day 1-{F1}", "place": c1},
            {"day_range": f"Day {F1}-{F2}", "place": c2},
            {"day_range": f"Day {F2}-{total_days}", "place": c3},
        ]

        solutions.append({
            "order": order,
            "flights": [(c1, c2, F1), (c2, c3, F2)],
            "segments": segments
        })

    if not solutions:
        raise RuntimeError("No valid itinerary found that satisfies all constraints.")

    # Choose an optimal solution.
    # Criteria: minimal flights (all equal), earliest first flight day, then lexicographically smallest order.
    solutions.sort(key=lambda s: (s["flights"][0][2], s["order"]))
    best = solutions[0]
    return {"itinerary": best["segments"]}

if __name__ == "__main__":
    # Input variables based on the given constraints
    total_days = 18
    city_durations = {
        "Split": 6,
        "Santorini": 7,
        "London": 7
    }
    # Direct flights (undirected)
    direct_flights = [
        ("London", "Santorini"),
        ("Split", "London"),
    ]
    # Conference requirements: must be in 'city' on 'day'
    conference_requirements = {
        12: "Santorini",
        18: "Santorini",
    }

    result = find_itinerary(total_days, city_durations, direct_flights, conference_requirements)
    print(json.dumps(result))