import json
import itertools

def compute_itinerary():
    # Input variables (trip constraints)
    total_days = 16
    cities = ["Dubrovnik", "Munich", "Krakow", "Split", "Milan", "Porto"]
    required_days = {
        "Dubrovnik": 4,
        "Split": 3,
        "Milan": 3,
        "Porto": 4,
        "Krakow": 2,
        "Munich": 5,
    }
    # Must-cover windows: city must include all days within each range (inclusive)
    must_cover = {
        "Munich": [(4, 8)],   # Annual show days
        "Milan": [(11, 13)],  # Wedding window
        "Krakow": [(8, 9)],   # Friends meetup window
    }
    # Direct flight adjacency (undirected)
    direct_flights_pairs = [
        ("Munich", "Porto"),
        ("Split", "Milan"),
        ("Milan", "Porto"),
        ("Munich", "Krakow"),
        ("Munich", "Milan"),
        ("Dubrovnik", "Munich"),
        ("Krakow", "Split"),
        ("Krakow", "Milan"),
        ("Munich", "Split"),
    ]
    direct_flights = set(frozenset(p) for p in direct_flights_pairs)

    # Quick checks on consistency: sum of city days must equal total_days + transitions
    # transitions = number of adjacent pairs = number_of_cities - 1
    if sum(required_days[c] for c in cities) != total_days + (len(cities) - 1):
        raise ValueError("Inconsistent total days vs per-city days and transitions.")

    def has_direct(a, b):
        return frozenset((a, b)) in direct_flights

    def compute_segments(order):
        # Compute start and end days for each city in the given order.
        # For segments: s1=1, e1=s1 + D1 - 1; s2=e1; e2=s2 + D2 - 1; ...
        segments = {}
        current_start = 1
        for city in order:
            d = required_days[city]
            s = current_start
            e = s + d - 1
            segments[city] = (s, e)
            current_start = e  # Next segment starts on the same day, enabling overlap (flight day)
        return segments

    def satisfies_must_cover(segments):
        for city, ranges in must_cover.items():
            s, e = segments[city]
            for lo, hi in ranges:
                if not (s <= lo and e >= hi):
                    return False
        return True

    def adjacency_ok(order):
        return all(has_direct(order[i], order[i+1]) for i in range(len(order)-1))

    def total_days_ok(segments, order):
        # The last segment must end on total_days.
        # With this segment chaining, this will hold if inputs are consistent,
        # but we validate anyway.
        last_city = order[-1]
        return segments[last_city][1] == total_days

    # Search over permutations to find a valid itinerary
    solution = None
    for order in itertools.permutations(cities):
        # Enforce that each city is visited exactly once (by design via permutation)

        # Quick pruning: Munich must cover 4-8 with exactly 5 days => Munich start must be day 4.
        # Compute the start day of Munich from partial sums without building full segments:
        # Start day s_i = 1 + sum_{j<i} D_j - (i-1)
        # We can skip permutations where that doesn't hold.
        idx_munich = order.index("Munich")
        sum_before = sum(required_days[order[j]] for j in range(idx_munich))
        s_munich = 1 + sum_before - idx_munich
        if s_munich != 4:
            continue

        # Krakow must start day 8 and last 2 days -> s=8,e=9; implies Krakow should follow Munich immediately.
        # Check that ordering enforces start day 8.
        # If Krakow is not immediately after Munich, s_K won't be 8 due to duration constraints.
        if idx_munich + 1 >= len(order) or order[idx_munich + 1] != "Krakow":
            continue

        # Milan must start day 11 -> with D=3 covers 11-13.
        # After Krakow (2 days, starting at 8 ending 9), the next city must end on day 11 (start 9, D must be 3).
        # Thus the city between Krakow and Milan must be Split.
        idx_krakow = order.index("Krakow")
        if not (idx_krakow + 1 < len(order) and order[idx_krakow + 1] == "Split"):
            continue
        if not (idx_krakow + 2 < len(order) and order[idx_krakow + 2] == "Milan"):
            continue

        # Additionally, because Milan must be followed by a city reachable directly and accommodating remaining days,
        # Porto must come after Milan (since Milan->Dubrovnik direct is not listed).
        idx_milan = order.index("Milan")
        if idx_milan + 1 >= len(order):
            continue
        if order[idx_milan + 1] != "Porto":
            continue

        # Compute full segments and validate constraints thoroughly
        segments = compute_segments(order)
        if not satisfies_must_cover(segments):
            continue
        if not adjacency_ok(order):
            continue
        if not total_days_ok(segments, order):
            continue

        solution = (order, segments)
        break

    if solution is None:
        raise RuntimeError("No feasible itinerary found under the given constraints.")

    order, segments = solution
    itinerary = []
    for city in order:
        s, e = segments[city]
        itinerary.append({"day_range": f"Day {s}-{e}", "place": city})

    return {"itinerary": itinerary}

if __name__ == "__main__":
    result = compute_itinerary()
    print(json.dumps(result))