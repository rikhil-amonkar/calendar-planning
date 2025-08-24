import json
from itertools import permutations

def compute_itinerary():
    # Input variables (trip constraints)
    total_days = 21
    city_days = {
        "Manchester": 3,
        "Istanbul": 7,
        "Venice": 7,
        "Krakow": 6,
        "Lyon": 2
    }
    # Direct flight pairs (undirected)
    direct_pairs = {
        ("Manchester", "Venice"),
        ("Manchester", "Istanbul"),
        ("Venice", "Istanbul"),
        ("Istanbul", "Krakow"),
        ("Venice", "Lyon"),
        ("Lyon", "Istanbul"),
        ("Manchester", "Krakow"),
    }
    direct = direct_pairs | {(b, a) for (a, b) in direct_pairs}

    # Presence windows: must be in the city for the full inclusive range
    presence_windows = {
        "Manchester": (1, 3),  # wedding between day 1 and day 3
        "Venice": (3, 9),      # workshop between day 3 and day 9
    }

    cities = list(city_days.keys())

    # Validate feasibility of global day arithmetic: sum(city_days) - (flights) == total_days
    # For a linear visit of all 5 cities, flights = 4 (n-1).
    if sum(city_days.values()) - (len(cities) - 1) != total_days:
        raise ValueError("Inconsistent total day arithmetic; no solution possible with given durations.")

    feasible_plans = []

    for order in permutations(cities):
        # Enforce direct flight connectivity between consecutive cities
        if not all((order[i], order[i + 1]) in direct for i in range(len(order) - 1)):
            continue

        # Build schedule with overlap on flight days:
        # Each next city starts on the same day the previous city ends (double-count flight day)
        schedule = {}
        start = 1
        for city in order:
            end = start + city_days[city] - 1
            schedule[city] = (start, end)
            start = end  # next city overlaps on this day

        # Ensure the final day matches the total trip horizon
        if schedule[order[-1]][1] != total_days:
            continue

        # Check presence windows: city interval must fully cover the window
        windows_ok = True
        slack = 0  # objective: minimize slack from exact window coverage
        for city, (ws, we) in presence_windows.items():
            cs, ce = schedule[city]
            if cs > ws or ce < we:
                windows_ok = False
                break
            # Minimize extra slack outside the required window
            slack += (ws - cs) ** 2 + (ce - we) ** 2

        if not windows_ok:
            continue

        feasible_plans.append((slack, order, schedule))

    if not feasible_plans:
        raise RuntimeError("No feasible itinerary found that satisfies all constraints and direct flight rules.")

    # Choose plan with minimal slack (exact window match preferred), tie-breaker: lexicographic order
    feasible_plans.sort(key=lambda x: (x[0], x[1]))
    _, best_order, best_schedule = feasible_plans[0]

    itinerary = [
        {"day_range": f"Day {best_schedule[city][0]}-{best_schedule[city][1]}", "place": city}
        for city in best_order
    ]

    return {"itinerary": itinerary}

if __name__ == "__main__":
    result = compute_itinerary()
    print(json.dumps(result, ensure_ascii=False))