import json
from itertools import permutations

def build_adjacency(flight_statements):
    adj = {}
    def add_city(c):
        if c not in adj:
            adj[c] = set()
    for stmt in flight_statements:
        stmt = stmt.strip()
        if stmt.lower().startswith("from "):
            # format: from A to B
            s = stmt[5:]
            parts = s.split(" to ")
            a = parts[0].strip()
            b = parts[1].strip()
            add_city(a); add_city(b)
            adj[a].add(b)
        else:
            # format: A and B (bidirectional)
            parts = stmt.split(" and ")
            a = parts[0].strip()
            b = parts[1].strip()
            add_city(a); add_city(b)
            adj[a].add(b)
            adj[b].add(a)
    return adj

def compute_day_ranges(order, durations):
    # order is full list of cities including last city
    day_ranges = []
    current_start = 1
    for city in order:
        d = durations[city]
        start = current_start
        end = start + d - 1
        day_ranges.append((city, start, end))
        # flight day overlaps: next start equals this end
        current_start = end
    return day_ranges

def validate_itinerary(order, durations, adj, total_days, windows):
    # order includes all cities with Oslo last
    # Check adjacency
    for i in range(len(order) - 1):
        if order[i+1] not in adj.get(order[i], set()):
            return False
    # Compute day ranges
    dr = compute_day_ranges(order, durations)
    # Validate total unique days end
    if dr[-1][2] != total_days:
        return False
    # Validate per-city durations
    for city, start, end in dr:
        if (end - start + 1) != durations[city]:
            return False
    # Validate wedding in Tallinn between day 4 and 8 (inclusive)
    # We interpret as: the span in Tallinn must cover all days 4..8
    tallinn_range = next((start_end for c, *start_end in dr if c == "Tallinn"), None)
    if tallinn_range is None:
        return False
    t_start, t_end = tallinn_range
    w_start, w_end = windows["Tallinn_wedding"]
    if not (t_start <= w_start and t_end >= w_end):
        return False
    # Validate meeting friend in Oslo between day 24 and 25 (inclusive: at least one of these days)
    oslo_range = next((start_end for c, *start_end in dr if c == "Oslo"), None)
    if oslo_range is None:
        return False
    o_start, o_end = oslo_range
    f_start, f_end = windows["Oslo_meet"]
    if not (o_start <= f_end and o_end >= f_start):
        return False
    return True

def find_itinerary(cities, durations, adj, total_days, windows):
    # We need a path visiting each city exactly once, ending at Oslo,
    # satisfying direct flights and day-window constraints.
    # Use DFS with pruning, keeping Oslo last.
    all_cities = list(cities)
    assert "Oslo" in all_cities
    others = [c for c in all_cities if c != "Oslo"]

    # Precompute (d-1) for pruning on Tallinn start day
    d_minus_1 = {c: durations[c] - 1 for c in all_cities}

    solution = None

    # Order candidates in a heuristic way: try cities with more outbound edges earlier to reduce dead-ends
    others_sorted = sorted(
        others,
        key=lambda c: (-len(adj.get(c, [])), -durations[c], c)
    )

    def dfs(path, used, accum_d_minus1):
        nonlocal solution
        if solution is not None:
            return
        # Prune based on Tallinn start day: if Tallinn not in path yet and accum >= 4, impossible to start at day 4
        if "Tallinn" not in path and accum_d_minus1 >= 4:
            return
        # If Tallinn is in path, ensure its start day == 4
        if "Tallinn" in path:
            # start_day = 1 + sum(d-1) of cities before Tallinn
            idx = path.index("Tallinn")
            accum_before_tallinn = sum(d_minus_1[path[j]] for j in range(idx))
            if 1 + accum_before_tallinn != 4:
                return

        if len(path) == len(others_sorted):
            # Check edge from last of path to Oslo
            if "Oslo" not in adj.get(path[-1], set()):
                return
            # Build full order
            full_order = path + ["Oslo"]
            # Validate complete itinerary
            if validate_itinerary(full_order, durations, adj, total_days, windows):
                solution = full_order
            return

        for cand in others_sorted:
            if cand in used:
                continue
            # adjacency check
            if path:
                prev = path[-1]
                if cand not in adj.get(prev, set()):
                    continue
            # compute new accum d-1
            new_accum = accum_d_minus1 + d_minus_1[cand]
            # Further pruning: ensure there is at least one outgoing option from cand (except when it will be the last before Oslo)
            # We check that cand has an edge to some city not yet used (or Oslo if it will be last before Oslo).
            # This is a light prune; skip if true dead-end.
            remaining_after = len(others_sorted) - (len(path) + 1)
            next_possible = False
            if remaining_after == 0:
                # next is Oslo, check edge cand->Oslo
                next_possible = "Oslo" in adj.get(cand, set())
            else:
                for nx in others_sorted:
                    if nx in used or nx == cand:
                        continue
                    if nx in adj.get(cand, set()):
                        next_possible = True
                        break
            if not next_possible:
                continue

            used.add(cand)
            path.append(cand)
            dfs(path, used, new_accum)
            path.pop()
            used.remove(cand)

    dfs([], set(), 0)
    return solution

def main():
    # Input variables (constraints)
    total_days = 25
    city_durations = {
        "Oslo": 2,
        "Helsinki": 2,
        "Edinburgh": 3,
        "Riga": 2,
        "Tallinn": 5,
        "Budapest": 5,
        "Vilnius": 5,
        "Porto": 5,
        "Geneva": 4,
    }
    # Direct flights list (as given)
    flight_statements = [
        "Porto and Oslo",
        "Edinburgh and Budapest",
        "Edinburgh and Geneva",
        "from Riga to Tallinn",
        "Edinburgh and Porto",
        "Vilnius and Helsinki",
        "from Tallinn to Vilnius",
        "Riga and Oslo",
        "Geneva and Oslo",
        "Edinburgh and Oslo",
        "Edinburgh and Helsinki",
        "Vilnius and Oslo",
        "Riga and Helsinki",
        "Budapest and Geneva",
        "Helsinki and Budapest",
        "Helsinki and Oslo",
        "Edinburgh and Riga",
        "Tallinn and Helsinki",
        "Geneva and Porto",
        "Budapest and Oslo",
        "Helsinki and Geneva",
        "from Riga to Vilnius",
        "Tallinn and Oslo",
    ]
    # Special windows
    windows = {
        "Tallinn_wedding": (4, 8),
        "Oslo_meet": (24, 25),
    }

    # Build adjacency
    adjacency = build_adjacency(flight_statements)

    # Find itinerary order
    cities = set(city_durations.keys())
    order = find_itinerary(cities, city_durations, adjacency, total_days, windows)
    if not order:
        # Fallback: No itinerary found
        output = {"error": "No feasible itinerary found given the constraints."}
        print(json.dumps(output))
        return

    # Compute day ranges
    ranges = compute_day_ranges(order, city_durations)

    itinerary = []
    for city, start, end in ranges:
        itinerary.append({
            "day_range": f"Day {start}-{end}",
            "place": city
        })

    print(json.dumps({"itinerary": itinerary}))

if __name__ == "__main__":
    main()