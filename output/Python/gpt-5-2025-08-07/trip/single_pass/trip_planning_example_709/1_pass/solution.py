import json
from collections import defaultdict

def build_adjacency(direct_flights):
    adj = defaultdict(set)
    for a, b in direct_flights:
        adj[a].add(b)
        adj[b].add(a)
    return adj

def hamiltonian_paths(adj, nodes, start, end):
    # DFS to generate all Hamiltonian paths from start to end
    n = len(nodes)
    target_set = set(nodes)
    paths = []

    def dfs(path, visited):
        if len(path) == n:
            if path[-1] == end:
                paths.append(path[:])
            return
        last = path[-1]
        for nxt in sorted(adj[last]):  # deterministic order
            if nxt not in visited:
                path.append(nxt)
                visited.add(nxt)
                dfs(path, visited)
                visited.remove(nxt)
                path.pop()

    dfs([start], {start})
    return paths

def build_schedule(order, durations, total_days):
    # Assign day ranges with 1-day overlaps at each transition (flight day counts for both cities)
    schedule = {}
    current_start = 1
    for city in order:
        s = durations[city]
        start = current_start
        end = start + s - 1
        schedule[city] = (start, end)
        current_start = end  # next city overlaps on the flight day
    # Validate total calendar end equals total_days
    if schedule[order[-1]][1] != total_days:
        return None
    return schedule

def intersects(a_start, a_end, b_start, b_end):
    return not (a_end < b_start or b_end < a_start)

def main():
    # Input variables (trip constraints)
    total_days = 18
    city_durations = {
        "Helsinki": 4,
        "Valencia": 5,
        "Dubrovnik": 4,
        "Porto": 3,
        "Prague": 3,
        "Reykjavik": 4,
    }
    direct_flights = [
        ("Helsinki", "Prague"),
        ("Prague", "Valencia"),
        ("Valencia", "Porto"),
        ("Helsinki", "Reykjavik"),
        ("Dubrovnik", "Helsinki"),
        ("Reykjavik", "Prague"),
    ]
    friend_city = "Porto"
    friend_window = (16, 18)  # inclusive

    # Build graph
    adj = build_adjacency(direct_flights)
    cities = list(city_durations.keys())

    # Check feasibility: total counted days and required flights
    total_counted_days = sum(city_durations.values())
    required_flights = total_counted_days - total_days
    if required_flights != len(cities) - 1:
        raise ValueError("Constraints are infeasible: flights needed vs. city count mismatch.")

    # Endpoints must be cities with degree 1 (leaves) to allow a Hamiltonian path in this graph
    degrees = {c: len(adj[c]) for c in cities}
    leaves = [c for c, d in degrees.items() if d == 1]
    # We expect Dubrovnik and Porto to be leaves
    # Generate candidate Hamiltonian paths using the two possible leaf endpoints
    candidates = []
    if len(leaves) >= 2:
        # Try both orientations of the leaf endpoints to find valid paths
        for start, end in [(leaves[0], leaves[1]), (leaves[1], leaves[0])]:
            candidates.extend(hamiltonian_paths(adj, cities, start, end))
    else:
        # Fallback: try all cities as potential starts/ends (unlikely needed here)
        for s in cities:
            for e in cities:
                if s != e:
                    candidates.extend(hamiltonian_paths(adj, cities, s, e))

    # Select a valid path that meets the friend-in-Porto window constraint
    chosen_order = None
    chosen_schedule = None
    for order in candidates:
        schedule = build_schedule(order, city_durations, total_days)
        if schedule is None:
            continue
        p_start, p_end = schedule[friend_city]
        if intersects(p_start, p_end, friend_window[0], friend_window[1]):
            chosen_order = order
            chosen_schedule = schedule
            break

    if not chosen_order:
        raise RuntimeError("No valid itinerary found that satisfies all constraints.")

    # Build output itinerary with day ranges
    itinerary = []
    for city in chosen_order:
        start, end = chosen_schedule[city]
        itinerary.append({
            "day_range": f"Day {start}-{end}",
            "place": city
        })

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()