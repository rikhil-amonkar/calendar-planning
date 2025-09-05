import itertools
import json

def find_itinerary(cities_durations, flights, total_days, friend_city, friend_window):
    # Build undirected edge set for quick lookup
    edges = {frozenset((a, b)) for a, b in flights}
    cities = list(cities_durations.keys())
    n = len(cities)

    # Check feasibility of total flights vs. day counts
    sum_durations = sum(cities_durations.values())
    required_flights = sum_durations - total_days
    if required_flights != n - 1:
        raise ValueError("Infeasible constraints: sum(durations) - total_days must equal number_of_cities - 1")

    def is_path(order):
        return all(frozenset((order[i], order[i+1])) in edges for i in range(len(order)-1))

    def compute_x(order):
        # Endpoint cities have x = d - 1, internal have x = d - 2; must be >= 0
        x_vals = []
        for i, city in enumerate(order):
            d = cities_durations[city]
            if i == 0 or i == len(order) - 1:
                x = d - 1
            else:
                x = d - 2
            if x < 0:
                return None
            x_vals.append(x)
        return x_vals

    def compute_day_ranges(order, x_vals):
        # Construct ranges using overlap-on-boundary rule
        ranges = {}
        # First city
        s = 1
        e = x_vals[0] + 1
        ranges[order[0]] = (s, e)
        d_cursor = e  # last overlap day used (also end of previous)
        # Middle cities
        for i in range(1, len(order)-1):
            city = order[i]
            s = d_cursor  # overlaps with previous on this day
            e = d_cursor + x_vals[i] + 1  # unique x plus next overlap
            ranges[city] = (s, e)
            d_cursor = e
        # Last city
        last_city = order[-1]
        s = d_cursor
        e = d_cursor + x_vals[-1]  # only unique x after previous overlap
        ranges[last_city] = (s, e)
        return ranges

    def interval_intersection_len(a, b):
        # a and b are (start, end) inclusive
        start = max(a[0], b[0])
        end = min(a[1], b[1])
        return max(0, end - start + 1)

    best = None
    best_score = -1
    best_ranges = None

    # Prefer permutations with friend_city placed last to maximize overlap with end-window if possible
    # But still evaluate all and pick the best score.
    for order in itertools.permutations(cities):
        if not is_path(order):
            continue
        x_vals = compute_x(order)
        if x_vals is None:
            continue
        ranges = compute_day_ranges(order, x_vals)
        # Validate the final day equals total_days
        end_of_trip = ranges[order[-1]][1]
        if end_of_trip != total_days:
            continue
        friend_range = ranges[friend_city]
        score = interval_intersection_len(friend_range, friend_window)
        # Choose the itinerary with maximum overlap with the specified friend window
        if score > best_score:
            best_score = score
            best = order
            best_ranges = ranges

    if best is None or best_score <= 0:
        raise ValueError("No feasible itinerary meets the constraints (including friend meeting window).")

    # Build itinerary output in order
    itinerary = []
    for city in best:
        s, e = best_ranges[city]
        itinerary.append({"day_range": f"Day {s}-{e}", "place": city})

    return {"itinerary": itinerary}

if __name__ == "__main__":
    # Input variables (constraints)
    cities_durations = {
        "Helsinki": 4,
        "Valencia": 5,
        "Dubrovnik": 4,
        "Porto": 3,
        "Prague": 3,
        "Reykjavik": 4,
    }
    flights = [
        ("Helsinki", "Prague"),
        ("Prague", "Valencia"),
        ("Valencia", "Porto"),
        ("Helsinki", "Reykjavik"),
        ("Dubrovnik", "Helsinki"),
        ("Reykjavik", "Prague"),
    ]
    total_days = 18
    friend_city = "Porto"
    friend_window = (16, 18)  # inclusive

    result = find_itinerary(cities_durations, flights, total_days, friend_city, friend_window)
    print(json.dumps(result, ensure_ascii=False))