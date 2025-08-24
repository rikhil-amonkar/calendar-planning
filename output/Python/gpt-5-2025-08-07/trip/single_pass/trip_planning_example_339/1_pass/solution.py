import json
import itertools

def compute_itinerary():
    # Input variables (trip constraints)
    total_days = 17
    city_days_required = {
        "Warsaw": 2,
        "Budapest": 7,
        "Paris": 4,
        "Riga": 7,
    }
    start_city = "Warsaw"
    end_city = "Riga"
    # Event windows
    show_city = "Warsaw"
    show_window = (1, 2)  # inclusive
    wedding_city = "Riga"
    wedding_window = (11, 17)  # inclusive

    # Direct flights (undirected)
    direct_pairs = [
        ("Warsaw", "Budapest"),
        ("Warsaw", "Riga"),
        ("Budapest", "Paris"),
        ("Warsaw", "Paris"),
        ("Paris", "Riga"),
    ]
    direct = set(direct_pairs) | set((b, a) for a, b in direct_pairs)

    # Helper to check if a pair is a direct flight
    def is_direct(a, b):
        return (a, b) in direct

    # All cities involved
    cities = list(city_days_required.keys())

    # Number of legs equals number of flights
    legs_needed = len(cities) - 1

    # Basic feasibility: sum of per-city days must equal total_days + legs (overlap via flight days)
    if sum(city_days_required.values()) != total_days + legs_needed:
        return {"error": "Infeasible durations vs total days and flights"}

    # Enumerate possible orders: start with Warsaw, end with Riga, visit others in between
    intermediates = [c for c in cities if c not in (start_city, end_city)]
    best_plan = None

    for perm in itertools.permutations(intermediates):
        order = [start_city] + list(perm) + [end_city]

        # Check direct flights along the route
        if not all(is_direct(order[i], order[i+1]) for i in range(len(order)-1)):
            continue

        # Solve flight days t1, t2, t3 based on contiguous blocks and overlap-on-travel rule
        d1 = city_days_required[order[0]]
        d2 = city_days_required[order[1]]
        d3 = city_days_required[order[2]]
        d4_req = city_days_required[order[3]]

        t1 = d1
        t2 = t1 + d2 - 1
        t3 = t2 + d3 - 1

        # Compute resulting last city's days
        d4_calc = total_days - t3 + 1
        if d4_calc != d4_req:
            continue  # mismatch, not feasible

        # Check event constraints:
        # Show in Warsaw on days 1-2
        if order[0] != show_city or not (show_window[0] >= 1 and show_window[1] <= t1):
            continue

        # Wedding in Riga between day 11 and 17 (must intersect Riga block)
        riga_start = t3
        riga_end = total_days
        wedding_start, wedding_end = wedding_window
        intersects = max(riga_start, wedding_start) <= min(riga_end, wedding_end)
        if not (order[-1] == wedding_city and intersects):
            continue

        # Valid plan found; since all valid routes have equal legs, pick the first feasible
        itinerary = [
            {"day_range": f"Day {1}-{t1}", "place": order[0]},
            {"day_range": f"Day {t1}-{t2}", "place": order[1]},
            {"day_range": f"Day {t2}-{t3}", "place": order[2]},
            {"day_range": f"Day {t3}-{total_days}", "place": order[3]},
        ]
        best_plan = {"itinerary": itinerary}
        break

    if best_plan is None:
        return {"error": "No feasible itinerary found with given constraints and direct flights."}

    return best_plan

if __name__ == "__main__":
    result = compute_itinerary()
    print(json.dumps(result, ensure_ascii=False))