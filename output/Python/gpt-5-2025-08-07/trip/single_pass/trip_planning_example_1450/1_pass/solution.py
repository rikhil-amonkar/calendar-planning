import json

def build_flights():
    # Cities
    cities = [
        "Stockholm", "Hamburg", "Florence", "Istanbul", "Oslo",
        "Vilnius", "Santorini", "Munich", "Frankfurt", "Krakow"
    ]

    # Initialize adjacency as ordered lists to keep deterministic search
    adj = {c: [] for c in cities}

    def add_dir(a, b):
        if b not in adj[a]:
            adj[a].append(b)

    def add_bi(a, b):
        add_dir(a, b)
        add_dir(b, a)

    # Add flights as per constraints
    add_bi("Oslo", "Stockholm")
    add_bi("Krakow", "Frankfurt")
    add_bi("Krakow", "Istanbul")
    add_bi("Munich", "Stockholm")
    add_bi("Hamburg", "Stockholm")
    add_dir("Krakow", "Vilnius")
    add_bi("Oslo", "Istanbul")
    add_bi("Istanbul", "Stockholm")
    add_bi("Oslo", "Krakow")
    add_bi("Vilnius", "Istanbul")
    add_bi("Oslo", "Vilnius")
    add_bi("Frankfurt", "Istanbul")
    add_bi("Oslo", "Frankfurt")
    add_bi("Munich", "Hamburg")
    add_bi("Munich", "Istanbul")
    add_bi("Oslo", "Munich")
    add_bi("Frankfurt", "Florence")
    add_bi("Oslo", "Hamburg")
    add_bi("Vilnius", "Frankfurt")
    add_dir("Florence", "Munich")
    add_bi("Krakow", "Munich")
    add_bi("Hamburg", "Istanbul")
    add_bi("Frankfurt", "Stockholm")
    add_dir("Stockholm", "Santorini")
    add_bi("Frankfurt", "Munich")
    add_dir("Santorini", "Oslo")
    add_bi("Krakow", "Stockholm")
    add_dir("Vilnius", "Munich")
    add_bi("Frankfurt", "Hamburg")

    return adj

def compute_itinerary():
    # Input parameters
    trip_days = 32
    city_durations = {
        "Stockholm": 3,
        "Hamburg": 5,
        "Florence": 2,
        "Istanbul": 5,
        "Oslo": 5,
        "Vilnius": 5,
        "Santorini": 2,
        "Munich": 5,
        "Frankfurt": 4,
        "Krakow": 5
    }

    # Day window constraints
    must_city_windows = {
        "Krakow": (5, 9),     # inclusive start, inclusive end
        "Istanbul": (25, 29)
    }

    cities = list(city_durations.keys())
    flights = build_flights()

    # Helper to compute start and end given path and next city
    def next_span(path, next_city):
        if not path:
            s = 1
        else:
            # end day of last in path
            s_prev = 1
            e_prev = city_durations[path[0]]
            for i in range(1, len(path)):
                s_prev = e_prev
                e_prev = s_prev + city_durations[path[i]] - 1
            s = e_prev
        e = s + city_durations[next_city] - 1
        return s, e

    # Quick pruning: compute current end day of path
    def current_end(path):
        if not path:
            return 0
        e_prev = city_durations[path[0]]
        for i in range(1, len(path)):
            s_prev = e_prev
            e_prev = s_prev + city_durations[path[i]] - 1
        return e_prev

    # Pre-calc totals to verify final end day
    total_duration = sum(city_durations.values())
    # With N cities and N-1 flights, total end day = total_duration - (N-1)
    expected_end_day = total_duration - (len(cities) - 1)
    assert expected_end_day == trip_days, "Durations and flight-day overlap must sum to total trip days."

    best_path = []

    # Order cities to guide search deterministically (start with ones that make Krakow=Day5 feasible)
    start_order = ["Florence", "Frankfurt", "Munich", "Hamburg", "Vilnius", "Stockholm", "Oslo", "Istanbul", "Krakow"]

    # Recursive backtracking
    def backtrack(path, used):
        nonlocal best_path
        if best_path:
            return  # stop at first found solution

        # Prune on day windows not yet met
        e_cur = current_end(path)

        # If we have passed day 5 without placing Krakow, impossible
        if "Krakow" not in used and e_cur > must_city_windows["Krakow"][0]:
            return
        # If we have passed day 25 without placing Istanbul, impossible
        if "Istanbul" not in used and e_cur > must_city_windows["Istanbul"][0]:
            return

        # If complete, validate final end day and windows
        if len(path) == len(cities):
            if e_cur != trip_days:
                return
            # Validate windows
            spans = {}
            s_prev = 1
            e_prev = city_durations[path[0]]
            spans[path[0]] = (1, e_prev)
            for i in range(1, len(path)):
                s_prev = e_prev
                e_prev = s_prev + city_durations[path[i]] - 1
                spans[path[i]] = (s_prev, e_prev)

            for city, (req_s, req_e) in must_city_windows.items():
                if spans.get(city) != (req_s, req_e):
                    return
            best_path = list(path)
            return

        # Choose next city
        candidates = [c for c in start_order if c not in used] + [c for c in cities if c not in used and c not in start_order]
        for cand in candidates:
            # Flight adjacency constraint
            if path:
                prev = path[-1]
                if cand not in flights[prev]:
                    continue

            # Compute span for candidate
            s, e = next_span(path, cand)

            # Enforce exclusive start days for windowed cities
            # Krakow must start at day 5; no other city may start at day 5
            if cand == "Krakow":
                if s != must_city_windows["Krakow"][0] or e != must_city_windows["Krakow"][1]:
                    continue
            else:
                if s == must_city_windows["Krakow"][0]:
                    continue

            # Istanbul must start at day 25; no other city may start at day 25
            if cand == "Istanbul":
                if s != must_city_windows["Istanbul"][0] or e != must_city_windows["Istanbul"][1]:
                    continue
            else:
                if s == must_city_windows["Istanbul"][0]:
                    continue

            # If placing Istanbul or Krakow earlier than allowed (s < required start) - allowed only if equals; already enforced

            # Proceed
            used.add(cand)
            path.append(cand)
            backtrack(path, used)
            path.pop()
            used.remove(cand)
            if best_path:
                return

    backtrack([], set())

    if not best_path:
        raise RuntimeError("No feasible itinerary found under the given constraints.")

    # Build itinerary with day ranges
    itinerary = []
    s_prev = 1
    e_prev = city_durations[best_path[0]]
    itinerary.append({"day_range": f"Day {s_prev}-{e_prev}", "place": best_path[0]})
    for i in range(1, len(best_path)):
        s_prev = e_prev
        e_prev = s_prev + city_durations[best_path[i]] - 1
        itinerary.append({"day_range": f"Day {s_prev}-{e_prev}", "place": best_path[i]})

    return {"itinerary": itinerary}

if __name__ == "__main__":
    result = compute_itinerary()
    print(json.dumps(result))