import json
from itertools import permutations

def make_edges(pairs):
    edges = set()
    for a, b in pairs:
        edges.add((a, b))
        edges.add((b, a))
    return edges

def have_direct(a, b, edges):
    return (a, b) in edges

def compute_schedule(order, durations):
    # Given an order, compute (city, start, end) list following overlap rule: next start = prev end
    sched = []
    current_start = 1
    for i, city in enumerate(order):
        start = current_start
        end = start + durations[city] - 1
        sched.append((city, start, end))
        current_start = end  # overlap on travel day
    return sched

def windows_satisfied(sched, windows):
    # windows: city -> (win_start, win_end) must be fully contained in city's interval
    pos = {city: (start, end) for city, start, end in sched}
    for city, (a, b) in windows.items():
        s, e = pos[city]
        if not (s <= a and e >= b):
            return False
    return True

def edges_satisfied(order, edges):
    for i in range(1, len(order)):
        if not have_direct(order[i-1], order[i], edges):
            return False
    return True

def main():
    # Input variables (constraints)
    cities = [
        "Salzburg", "Venice", "Bucharest", "Brussels", "Hamburg",
        "Copenhagen", "Nice", "Zurich", "Naples"
    ]
    durations = {
        "Salzburg": 2,
        "Venice": 5,
        "Bucharest": 4,
        "Brussels": 2,
        "Hamburg": 4,
        "Copenhagen": 4,
        "Nice": 3,
        "Zurich": 5,
        "Naples": 4,
    }
    total_days = 25

    # Time-window requirements (inclusive day numbers)
    windows = {
        "Brussels": (21, 22),           # meet friends between day 21 and day 22; also 2-day stay
        "Copenhagen": (18, 21),         # wedding between day 18 and day 21; 4-day stay
        "Nice": (9, 11),                # visit relatives between day 9 and day 11; 3-day stay
        "Naples": (22, 25),             # workshop between day 22 and day 25; 4-day stay
    }

    # Direct flight pairs (undirected)
    flight_pairs = [
        ("Zurich", "Brussels"),
        ("Bucharest", "Copenhagen"),
        ("Venice", "Brussels"),
        ("Nice", "Zurich"),
        ("Hamburg", "Nice"),
        ("Zurich", "Naples"),
        ("Hamburg", "Bucharest"),
        ("Zurich", "Copenhagen"),
        ("Bucharest", "Brussels"),
        ("Hamburg", "Brussels"),
        ("Venice", "Naples"),
        ("Venice", "Copenhagen"),
        ("Bucharest", "Naples"),
        ("Hamburg", "Copenhagen"),
        ("Venice", "Zurich"),
        ("Nice", "Brussels"),
        ("Hamburg", "Venice"),
        ("Copenhagen", "Naples"),
        ("Nice", "Naples"),
        ("Hamburg", "Zurich"),
        ("Salzburg", "Hamburg"),
        ("Zurich", "Bucharest"),
        ("Brussels", "Naples"),
        ("Copenhagen", "Brussels"),
        ("Venice", "Nice"),
        ("Nice", "Copenhagen"),
    ]
    edges = make_edges(flight_pairs)

    # Basic validation: durations sum must equal total_days + number_of_flights (which is len(cities)-1) for a linear path with overlap on flight days
    if sum(durations[c] for c in cities) != total_days + (len(cities) - 1):
        raise ValueError("Durations do not sum to total_days + transitions; cannot form a linear overlapped itinerary.")

    # Identify "anchored" cities whose window length equals their duration; those must start exactly at window start
    anchored_starts = {}
    for city, (a, b) in windows.items():
        if durations[city] == (b - a + 1):
            anchored_starts[city] = a

    # We expect Nice (9), Copenhagen (18), Brussels (21), Naples (22) to be anchored
    # Derive that the cities with the three latest anchored starts must form the suffix in ascending start order
    anchored_sorted = sorted(anchored_starts.items(), key=lambda kv: kv[1])  # list of (city, start)
    # Last three anchored by start day
    suffix_anchors = [city for city, _ in anchored_sorted[-3:]]  # should be ["Copenhagen","Brussels","Naples"] order by start
    # Ensure ascending order by anchored start day among suffix anchors
    suffix_anchors = sorted(suffix_anchors, key=lambda c: anchored_starts[c])
    # Validate that Naples is last by having the max start
    if suffix_anchors[-1] != "Naples":
        # In this specific problem, Naples must be the final city to end on day 25
        pass  # Not strictly necessary to raise; the search/validation will enforce correctness

    # Salzburg has degree 1 (only direct to Hamburg), so it must be at an end. Because Naples must end on day 25,
    # Salzburg must be at the start.
    # We will fix:
    #   order = [Salzburg, Hamburg, ?, ?, ?, ?, Copenhagen, Brussels, Naples]
    # and search over permutations for the four middle slots while enforcing Nice's anchored start (9).
    start_fixed = ["Salzburg", "Hamburg"]
    suffix_fixed = ["Copenhagen", "Brussels", "Naples"]

    middle_candidates = [c for c in cities if c not in start_fixed + suffix_fixed]
    # middle_candidates should be ["Venice","Bucharest","Nice","Zurich"]

    solution = None

    for mid_perm in permutations(middle_candidates, 4):
        order = start_fixed + list(mid_perm) + suffix_fixed

        # Quick adjacency pruning for fixed Salzburg->Hamburg and middle chain + suffix
        if not edges_satisfied(order, edges):
            continue

        # Compute schedule
        sched = compute_schedule(order, durations)

        # Enforce that anchored cities start on their anchored start day
        anchored_ok = True
        for city, anchor_start in anchored_starts.items():
            for c, s, e in sched:
                if c == city:
                    if s != anchor_start:
                        anchored_ok = False
                    break
            if not anchored_ok:
                break
        if not anchored_ok:
            continue

        # Enforce all windows fully contained
        if not windows_satisfied(sched, windows):
            continue

        # Verify total days end at 25 for the last city
        if sched[-1][2] != total_days:
            continue

        solution = sched
        break

    if solution is None:
        raise RuntimeError("No valid itinerary found under the given constraints.")

    # Build JSON output
    itinerary = []
    for city, start, end in solution:
        itinerary.append({
            "day_range": f"Day {start}-{end}",
            "place": city
        })

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()