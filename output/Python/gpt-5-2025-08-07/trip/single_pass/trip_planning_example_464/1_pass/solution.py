import itertools
import json

def build_adjacency(direct_flights):
    adj = set()
    for a, b in direct_flights:
        adj.add((a, b))
        adj.add((b, a))
    return adj

def is_direct(a, b, adj):
    return (a, b) in adj

def compute_schedule(order, durations):
    # Overlapping day at transitions: start_next = end_current
    schedule = {}
    start = 1
    for city in order:
        d = durations[city]
        end = start + d - 1
        schedule[city] = (start, end)
        start = end  # overlap day counts for both
    return schedule

def overlap_length(a_range, b_range):
    a_start, a_end = a_range
    b_start, b_end = b_range
    lo = max(a_start, b_start)
    hi = min(a_end, b_end)
    return max(0, hi - lo + 1)

def format_itinerary(order, schedule):
    items = []
    for city in order:
        start, end = schedule[city]
        items.append({"day_range": f"Day {start}-{end}", "place": city})
    return items

def main():
    # Input variables (constraints)
    total_days = 18
    required_durations = {
        "Krakow": 5,
        "Frankfurt": 4,
        "Oslo": 3,
        "Dubrovnik": 5,
        "Naples": 5,
    }
    cities = list(required_durations.keys())
    num_cities = len(cities)

    # Direct flight pairs (undirected)
    direct_flights = [
        ("Dubrovnik", "Oslo"),
        ("Frankfurt", "Krakow"),
        ("Frankfurt", "Oslo"),
        ("Dubrovnik", "Frankfurt"),
        ("Krakow", "Oslo"),
        ("Naples", "Oslo"),
        ("Naples", "Dubrovnik"),
        ("Naples", "Frankfurt"),
    ]
    adjacency = build_adjacency(direct_flights)

    # Special windows
    oslo_window = (16, 18)  # must be in Oslo on days 16-18 (3 days total)
    dubrovnik_window = (5, 9)  # want to be in Dubrovnik between day 5 and day 9

    # Feasibility check: total calendar days = sum(durations) - (num_cities-1)
    sum_durations = sum(required_durations.values())
    implied_total = sum_durations - (num_cities - 1)
    if implied_total != total_days:
        raise ValueError(f"Inconsistent total days: durations imply {implied_total}, but total_days is {total_days}")

    # Generate candidate orders: enforce Oslo last to satisfy its specific window
    other_cities = [c for c in cities if c != "Oslo"]
    best = None  # (score_tuple, order, schedule)
    for perm in itertools.permutations(other_cities):
        order = list(perm) + ["Oslo"]

        # Check all transitions are direct flights
        if not all(is_direct(order[i], order[i+1], adjacency) for i in range(len(order)-1)):
            continue

        # Compute schedule
        schedule = compute_schedule(order, required_durations)

        # Validate overall days end
        last_city = order[-1]
        if schedule[last_city][1] != total_days:
            continue

        # Oslo window check: must cover 16-18 inclusive
        oslo_range = schedule["Oslo"]
        if overlap_length(oslo_range, oslo_window) != (oslo_window[1] - oslo_window[0] + 1):
            continue

        # Dubrovnik window: must overlap at least 1 day; prefer maximizing overlap
        dubrovnik_range = schedule["Dubrovnik"]
        dubrovnik_overlap = overlap_length(dubrovnik_range, dubrovnik_window)
        if dubrovnik_overlap <= 0:
            continue

        # Scoring:
        # - Primary: maximize Dubrovnik overlap with [5,9] (i.e., minimize negative overlap)
        # - Secondary: earliest meeting day within window (smaller is better)
        # - Tertiary: lexicographic order for determinism
        earliest_meet_day = max(dubrovnik_range[0], dubrovnik_window[0])
        score = (-dubrovnik_overlap, earliest_meet_day, tuple(order))
        if best is None or score < best[0]:
            best = (score, order, schedule)

    if best is None:
        # No valid itinerary found with given constraints
        result = {"itinerary": []}
    else:
        _, order, schedule = best
        itinerary = format_itinerary(order, schedule)
        result = {"itinerary": itinerary}

    print(json.dumps(result, ensure_ascii=False))

if __name__ == "__main__":
    main()