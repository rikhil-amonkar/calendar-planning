import json
import itertools

def compute_itinerary():
    # Input variables (trip constraints)
    total_days = 23
    cities = [
        "Edinburgh",
        "Amsterdam",
        "Vienna",
        "Reykjavik",
        "Berlin",
        "Brussels",
    ]
    durations = {
        "Amsterdam": 4,
        "Edinburgh": 5,
        "Brussels": 5,
        "Vienna": 5,
        "Berlin": 4,
        "Reykjavik": 5,
    }
    # Windows are inclusive: must be in the city for all days in [start, end]
    windows = {
        "Amsterdam": (5, 8),     # visit relatives
        "Reykjavik": (12, 16),   # workshop
        "Berlin": (16, 19),      # meet friend
    }
    # Direct flights (undirected)
    direct_pairs = [
        ("Edinburgh", "Berlin"),
        ("Amsterdam", "Berlin"),
        ("Edinburgh", "Amsterdam"),
        ("Vienna", "Berlin"),
        ("Berlin", "Brussels"),
        ("Vienna", "Brussels"),
        ("Edinburgh", "Brussels"),
        ("Vienna", "Reykjavik"),
        ("Amsterdam", "Reykjavik"),
        ("Reykjavik", "Brussels"),
        ("Amsterdam", "Vienna"),
        ("Reykjavik", "Berlin"),
    ]
    direct = set(frozenset(pair) for pair in direct_pairs)

    # Basic feasibility check: sum(durations) must equal total_days + (n_cities - 1)
    total_duration = sum(durations[c] for c in cities)
    n = len(cities)
    if total_duration != total_days + (n - 1):
        raise ValueError("Inconsistent durations vs total days and transitions.")

    # The start day of the first city is fixed by total span arithmetic
    # end_last = start_first + total_duration - n
    # To make end_last == total_days, start_first must be:
    start_first = total_days - (total_duration - n)

    def consecutive_direct(order):
        for i in range(len(order) - 1):
            if frozenset((order[i], order[i+1])) not in direct:
                return False
        return True

    def build_schedule(order):
        # Compute start/end days based on order, durations, and 1-day overlap at each flight
        starts = {}
        ends = {}
        cur_start = start_first
        for idx, city in enumerate(order):
            if idx == 0:
                s = cur_start
            else:
                # transition day overlaps: start of this city equals end of previous city
                s = ends[order[idx - 1]]
            e = s + durations[city] - 1
            starts[city] = s
            ends[city] = e
        return starts, ends

    def windows_satisfied(starts, ends):
        for city, (a, b) in windows.items():
            # Must include entire window [a, b]
            if not (starts[city] <= a and ends[city] >= b):
                return False
        # Also ensure bounds are within trip days
        for city in cities:
            if starts[city] < 1 or ends[city] > total_days:
                return False
        return True

    feasible_order = None
    feasible_schedule = None

    # Try all permutations that satisfy direct-flight adjacency and windows
    for order in itertools.permutations(cities):
        if not consecutive_direct(order):
            continue
        starts, ends = build_schedule(order)
        # Ensure the last city ends on the final trip day (should be guaranteed by start_first)
        last_city = order[-1]
        if ends[last_city] != total_days:
            continue
        if windows_satisfied(starts, ends):
            feasible_order = order
            feasible_schedule = (starts, ends)
            break

    if feasible_order is None:
        raise RuntimeError("No feasible itinerary found given the constraints.")

    # Build JSON output
    starts, ends = feasible_schedule
    itinerary = []
    for city in feasible_order:
        itinerary.append({
            "day_range": f"Day {starts[city]}-{ends[city]}",
            "place": city
        })

    return {"itinerary": itinerary}

if __name__ == "__main__":
    result = compute_itinerary()
    print(json.dumps(result, ensure_ascii=False))