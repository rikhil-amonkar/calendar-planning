import json
from itertools import permutations

def compute_itinerary(total_days, desired_stays, mandatory_windows, direct_flights):
    # Build adjacency for undirected direct flights
    adjacency = {}
    for a, b in direct_flights:
        adjacency.setdefault(a, set()).add(b)
        adjacency.setdefault(b, set()).add(a)

    cities = list(desired_stays.keys())
    n_cities = len(cities)

    # Basic feasibility check: sum of stays must equal total_days + (n_cities - 1)
    # because each flight day is counted twice (overlap between consecutive cities).
    if sum(desired_stays.values()) != total_days + (n_cities - 1):
        raise ValueError("Infeasible durations: sum(desired_stays) must equal total_days + (number_of_cities - 1).")

    # Determine start and end cities from mandatory windows (earliest start -> start city, latest end -> end city)
    if not mandatory_windows:
        raise ValueError("At least one mandatory window needed to anchor the route.")
    # Sort windows by start and end to find start and end anchors
    windows_by_start = sorted(mandatory_windows.items(), key=lambda kv: kv[1][0])
    windows_by_end = sorted(mandatory_windows.items(), key=lambda kv: kv[1][1])
    start_city = windows_by_start[0][0]
    end_city = windows_by_end[-1][0]

    # We require the start window to begin on day 1 and the end window to end on total_days
    start_window = mandatory_windows[start_city]
    end_window = mandatory_windows[end_city]
    if start_window[0] != 1:
        raise ValueError("Start city's mandatory window must begin on Day 1 for this solver.")
    if end_window[1] != total_days:
        raise ValueError("End city's mandatory window must end on the last day for this solver.")

    # Middle cities are the remaining ones
    middle_cities = [c for c in cities if c not in {start_city, end_city}]

    # Try all middle city permutations to find a route that uses only direct flights
    candidate_routes = []
    for perm in permutations(middle_cities):
        route = [start_city] + list(perm) + [end_city]
        # Check direct flights between consecutive cities
        ok = True
        for i in range(len(route) - 1):
            a, b = route[i], route[i+1]
            if b not in adjacency.get(a, set()):
                ok = False
                break
        if not ok:
            continue

        # Build the schedule using inclusive overlap: each leg overlaps by 1 day (flight day)
        # Segment i covers [s_i, e_i], where:
        # s_1 = 1
        # e_i = s_i + d_i - 1
        # s_{i+1} = e_i  (overlap on the flight day)
        spans = []
        s = 1
        feasible = True
        for city in route:
            d = desired_stays[city]
            e = s + d - 1
            spans.append((city, s, e))
            s = e  # next segment starts on this same day (overlap)
        # After last segment, its end day must match total_days
        last_city, s_last, e_last = spans[-1]
        if e_last != total_days:
            feasible = False

        # Check mandatory windows are satisfied: each window must be subset of its city's [s,e]
        for city_w, (w_s, w_e) in mandatory_windows.items():
            # find span for city_w
            c_span = next((x for x in spans if x[0] == city_w), None)
            if c_span is None:
                feasible = False
                break
            _, c_s, c_e = c_span
            if not (c_s <= w_s and w_e <= c_e):
                feasible = False
                break

        if feasible:
            candidate_routes.append(spans)

    if not candidate_routes:
        raise ValueError("No feasible route found that satisfies direct flights and constraints.")

    # Select the first feasible route (could apply additional optimality criteria if needed)
    chosen_spans = candidate_routes[0]

    # Build itinerary output
    itinerary = []
    for city, s, e in chosen_spans:
        itinerary.append({
            "day_range": f"Day {s}-{e}",
            "place": city
        })

    return {"itinerary": itinerary}

def main():
    # Input variables (constraints)
    total_days = 15
    desired_stays = {
        "Stuttgart": 5,
        "Manchester": 7,
        "Madrid": 4,
        "Vienna": 2
    }
    mandatory_windows = {
        "Stuttgart": (11, 15),  # Workshop in Stuttgart between day 11 and day 15
        "Manchester": (1, 7)    # Wedding in Manchester between day 1 and day 7
    }
    direct_flights = [
        ("Vienna", "Stuttgart"),
        ("Manchester", "Vienna"),
        ("Madrid", "Vienna"),
        ("Manchester", "Stuttgart"),
        ("Manchester", "Madrid"),
    ]

    result = compute_itinerary(total_days, desired_stays, mandatory_windows, direct_flights)
    print(json.dumps(result, ensure_ascii=False))

if __name__ == "__main__":
    main()