import json
from collections import defaultdict

def build_adjacency(connections_text):
    graph = defaultdict(set)
    # Split by comma and parse each token
    tokens = [t.strip() for t in connections_text.strip().split(",")]
    for tok in tokens:
        tok = tok.strip()
        if not tok:
            continue
        if tok.endswith("."):
            tok = tok[:-1].strip()
        if tok.lower().startswith("from "):
            # format: from X to Y
            # find 'to'
            try:
                rest = tok[5:]  # after 'from '
                x, y = rest.split(" to ")
                x = x.strip()
                y = y.strip()
                graph[x].add(y)
            except Exception:
                pass
        else:
            # format: A and B
            if " and " in tok:
                a, b = tok.split(" and ")
                a = a.strip()
                b = b.strip()
                if a and b:
                    graph[a].add(b)
                    graph[b].add(a)
    return graph

def compute_itinerary():
    total_days = 32

    cities = [
        "Bucharest",
        "Krakow",
        "Munich",
        "Barcelona",
        "Warsaw",
        "Budapest",
        "Stockholm",
        "Riga",
        "Edinburgh",
        "Vienna",
    ]

    # Planned exact durations (days counted per rules; flight day counts for both cities)
    durations = {
        "Bucharest": 2,
        "Krakow": 4,
        "Munich": 3,
        "Barcelona": 5,
        "Warsaw": 5,
        "Budapest": 5,
        "Stockholm": 2,
        "Riga": 5,
        "Edinburgh": 5,
        "Vienna": 5,
    }

    # Required presence windows (inclusive). City must cover the entire window.
    windows = {
        "Edinburgh": (1, 5),     # meet friend between day 1 and day 5
        "Budapest": (9, 13),     # annual show 9-13
        "Stockholm": (17, 18),   # meet friends 17-18
        "Munich": (18, 20),      # workshop 18-20
        "Warsaw": (25, 29),      # conference 25-29
    }

    connections_text = (
        "Budapest and Munich, Bucharest and Riga, Munich and Krakow, Munich and Warsaw, "
        "Munich and Bucharest, Edinburgh and Stockholm, Barcelona and Warsaw, Edinburgh and Krakow, "
        "Barcelona and Munich, Stockholm and Krakow, Budapest and Vienna, Barcelona and Stockholm, "
        "Stockholm and Munich, Edinburgh and Budapest, Barcelona and Riga, Edinburgh and Barcelona, "
        "Vienna and Riga, Barcelona and Budapest, Bucharest and Warsaw, Vienna and Krakow, "
        "Edinburgh and Munich, Barcelona and Bucharest, Edinburgh and Riga, Vienna and Stockholm, "
        "Warsaw and Krakow, Barcelona and Krakow, from Riga to Munich, Vienna and Bucharest, "
        "Budapest and Warsaw, Vienna and Warsaw, Barcelona and Vienna, Budapest and Bucharest, "
        "Vienna and Munich, Riga and Warsaw, Stockholm and Riga, Stockholm and Warsaw."
    )
    graph = build_adjacency(connections_text)

    # Sanity check: sum durations must equal total_days + (n-1) due to shared flight days
    sum_d = sum(durations[c] for c in cities)
    if sum_d != total_days + (len(cities) - 1):
        raise ValueError("Infeasible durations vs total days and city count.")

    # Determine the unique first city (must cover day 1)
    starters = []
    for c in cities:
        if c in windows:
            L, U = windows[c]
            if L <= 1 <= U:
                starters.append(c)
    # If none have explicit window including day 1, allow any city that can start at day 1.
    if not starters:
        starters = cities[:]
    # Prefer the one with the tightest window starting at day 1 (if multiple)
    def starter_key(c):
        if c in windows:
            L, U = windows[c]
            return (L, U - L)  # earlier L, smaller window first
        return (float('inf'), float('inf'))
    starters.sort(key=starter_key)

    # Backtracking to find valid order and date assignment
    n = len(cities)
    all_cities_set = set(cities)

    best_order = None

    # Heuristic for candidate ordering at each step
    def candidate_sort_key(c):
        # Prefer those with windows earlier, then by longer duration, then name
        if c in windows:
            L, U = windows[c]
            return (L, -(U - L + 1), -durations[c], c)
        else:
            return (float('inf'), 0, -durations[c], c)

    def backtrack(order, e_prev):
        nonlocal best_order
        if best_order is not None:
            return  # stop at first solution

        if len(order) == n:
            # Check final day matches total_days
            if e_prev == total_days:
                # Verify all windows satisfied (should already be)
                best_order = order[:]
            return

        last_city = order[-1]
        s_next = e_prev  # next city's start (shared flight day)

        remaining = [c for c in cities if c not in order]
        # adjacency filter
        candidates = [c for c in remaining if c in graph[last_city]]

        # Sort by heuristic to guide search
        candidates.sort(key=candidate_sort_key)

        for c in candidates:
            s = s_next
            e = s + durations[c] - 1
            # prune if exceeds total days before finishing
            if e > total_days:
                continue
            # Window check for this city
            if c in windows:
                L, U = windows[c]
                if not (s <= L and e >= U):
                    continue

            # Additional simple forward checks:
            # 1) Remaining minimal and maximal possible end day feasibility (optional)
            #    Not strictly necessary due to equality, but we ensure we don't get stuck too early.
            #    Compute predicted final end if we order remaining arbitrarily (always equals total_days),
            #    so we skip this.

            order.append(c)
            backtrack(order, e)
            order.pop()
            if best_order is not None:
                return

    # Try each feasible starter
    for start in starters:
        # First city starts at day 1
        s1 = 1
        e1 = s1 + durations[start] - 1
        # Window check for first city
        if start in windows:
            L, U = windows[start]
            if not (s1 <= L and e1 >= U):
                continue
        # Backtrack
        backtrack([start], e1)
        if best_order is not None:
            break

    if best_order is None:
        raise RuntimeError("No feasible itinerary found with given constraints.")

    # Build the final itinerary with day ranges
    itinerary = []
    s = 1
    for i, city in enumerate(best_order):
        e = s + durations[city] - 1
        itinerary.append({
            "day_range": f"Day {s}-{e}",
            "place": city
        })
        s = e  # next starts on the same day (flight day)

    return {"itinerary": itinerary}

if __name__ == "__main__":
    result = compute_itinerary()
    print(json.dumps(result, ensure_ascii=False))