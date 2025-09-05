import json
from collections import defaultdict

def build_graph(edges):
    graph = defaultdict(set)
    for a, b in edges:
        graph[a].add(b)
        graph[b].add(a)
    return graph

def compute_itinerary(cities, durations, edges, include_windows, overlap_windows, total_days):
    # Build undirected graph of direct flights
    graph = build_graph(edges)

    # Derived constraints
    # Required exact start days when include-window covers full duration
    must_start_day = {}
    for city, (a, b) in include_windows.items():
        d = durations[city]
        if b - a + 1 == d:
            must_start_day[city] = a  # fixed start day
    # Convert to required sum_before (start day - 1)
    must_start_sum = {c: day - 1 for c, day in must_start_day.items()}

    # Sanity check: total unique days equals sum(durations) - n + 1 must equal total_days
    n = len(cities)
    sum_durations = sum(durations[c] for c in cities)
    unique_days = sum_durations - n + 1
    if unique_days != total_days:
        raise ValueError("Durations do not match required total days with overlap rule.")

    # Helper: check if candidate can be placed next at current sum_before
    def can_place(city, sum_before):
        # Start day for this city if placed now with x=1
        S = 1 + sum_before
        d = durations[city]
        # If city has exact start requirement
        if city in must_start_day and S != must_start_day[city]:
            return False
        # If city has include-window (must cover [a, b])
        win = include_windows.get(city)
        if win is not None:
            a, b = win
            if not (S <= a and S + d - 1 >= b):
                return False
        # If city has overlap-window (must overlap with [a, b])
        owin = overlap_windows.get(city)
        if owin is not None:
            a, b = owin
            if not (S <= b and S + d - 1 >= a):
                return False
        # Also, prune if this city has an exact required sum_before which is already passed
        if city in must_start_sum and sum_before > must_start_sum[city]:
            return False
        return True

    # DFS search for Hamiltonian path satisfying constraints and windows
    best_path = None

    # Start day anchor: by problem statement day numbering is from 1 and time windows are absolute,
    # and with the overlap model the end day auto becomes total_days when x=1.
    # We thus fix x=1 implicitly via sum_before indexing.

    cities_set = set(cities)

    # To reduce branching: if current sum_before equals a must_start_sum for a city not yet used,
    # the next city is forced to be that one.
    forced_positions = defaultdict(list)
    for c, ssum in must_start_sum.items():
        forced_positions[ssum].append(c)

    # Start candidates: prioritize Edinburgh to satisfy meeting window early
    start_candidates = sorted(cities)
    if "Edinburgh" in start_candidates:
        start_candidates.remove("Edinburgh")
        start_candidates.insert(0, "Edinburgh")

    def dfs(path, used, sum_before):
        nonlocal best_path
        if best_path is not None:
            return  # stop at first valid solution

        # If all cities placed, verify final day equals total_days (it will if durations sum matches)
        if len(path) == n:
            # Verify adjacency already ensured, verify all constraints satisfied
            # Compute last end day to ensure equals total_days
            end_last = 1 + (sum_durations - n)  # end_last = x + sum(d) - n, with x=1
            if end_last == total_days:
                best_path = list(path)
            return

        # If at a position where a city is forced by must_start_sum, enforce it
        forced_next = forced_positions.get(sum_before, [])
        candidates = []
        if forced_next:
            # If any forced city already used, no solution down this path
            forced_cands = [c for c in forced_next if c not in used]
            if len(forced_cands) == 0:
                return  # forced city already placed earlier, impossible
            # If multiple forced cities at same sum (shouldn't happen), try all
            candidates = forced_cands
        else:
            # Otherwise try all unused cities
            for c in cities:
                if c in used:
                    continue
                # Prune cities whose must_start_sum is in the past
                if c in must_start_sum and sum_before > must_start_sum[c]:
                    continue
                candidates.append(c)

            # Heuristic: prefer cities adjacent to last and those with tighter constraints
            # Define a sort key
            def cand_key(c):
                tight = 0
                if c in must_start_day:
                    tight -= 10
                if c == "Edinburgh":
                    tight -= 5
                deg = len(graph[c])
                return (tight, -deg, c)
            candidates.sort(key=cand_key)

        for c in candidates:
            # Adjacency check
            if path:
                prev = path[-1]
                if c not in graph[prev]:
                    continue
            # Window feasibility
            if not can_place(c, sum_before):
                continue

            # Place
            used.add(c)
            path.append(c)
            dfs(path, used, sum_before + (durations[c] - 1))
            path.pop()
            used.remove(c)
            if best_path is not None:
                return

    # Try starting from prioritized start candidates, ensuring their windows
    for start in start_candidates:
        if not can_place(start, 0):
            continue
        dfs([start], {start}, durations[start] - 1)
        if best_path is not None:
            break

    if best_path is None:
        raise RuntimeError("No feasible itinerary found under given constraints.")

    # Build final itinerary with day ranges
    itinerary = []
    sum_before = 0
    for c in best_path:
        start_day = 1 + sum_before
        end_day = start_day + durations[c] - 1
        itinerary.append({"day_range": f"Day {start_day}-{end_day}", "place": c})
        sum_before += durations[c] - 1

    return {"itinerary": itinerary}

if __name__ == "__main__":
    # Input variables (constraints)
    cities = [
        "Bucharest", "Krakow", "Munich", "Barcelona", "Warsaw",
        "Budapest", "Stockholm", "Riga", "Edinburgh", "Vienna"
    ]
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
        "Vienna": 5
    }
    # Direct flights (treated as undirected)
    edges = [
        ("Budapest", "Munich"),
        ("Bucharest", "Riga"),
        ("Munich", "Krakow"),
        ("Munich", "Warsaw"),
        ("Munich", "Bucharest"),
        ("Edinburgh", "Stockholm"),
        ("Barcelona", "Warsaw"),
        ("Edinburgh", "Krakow"),
        ("Barcelona", "Munich"),
        ("Stockholm", "Krakow"),
        ("Budapest", "Vienna"),
        ("Barcelona", "Stockholm"),
        ("Stockholm", "Munich"),
        ("Edinburgh", "Budapest"),
        ("Barcelona", "Riga"),
        ("Edinburgh", "Barcelona"),
        ("Vienna", "Riga"),
        ("Barcelona", "Budapest"),
        ("Bucharest", "Warsaw"),
        ("Vienna", "Krakow"),
        ("Edinburgh", "Munich"),
        ("Barcelona", "Bucharest"),
        ("Edinburgh", "Riga"),
        ("Vienna", "Stockholm"),
        ("Warsaw", "Krakow"),
        ("Barcelona", "Krakow"),
        ("Riga", "Munich"),  # from Riga to Munich (assumed undirected)
        ("Vienna", "Bucharest"),
        ("Budapest", "Warsaw"),
        ("Vienna", "Warsaw"),
        ("Barcelona", "Vienna"),
        ("Budapest", "Bucharest"),
        ("Vienna", "Munich"),
        ("Riga", "Warsaw"),
        ("Stockholm", "Riga"),
        ("Stockholm", "Warsaw"),
    ]
    # Include windows: city must cover the entire [a, b] (inclusive)
    include_windows = {
        "Budapest": (9, 13),   # 5 days, exact
        "Stockholm": (17, 18), # 2 days, exact
        "Munich": (18, 20),    # 3 days, exact
        "Warsaw": (25, 29)     # 5 days, exact
    }
    # Overlap windows: city must overlap at least one day with [a, b]
    overlap_windows = {
        "Edinburgh": (1, 5)    # must meet friend in day 1-5
    }
    total_days = 32

    result = compute_itinerary(cities, durations, edges, include_windows, overlap_windows, total_days)
    print(json.dumps(result))