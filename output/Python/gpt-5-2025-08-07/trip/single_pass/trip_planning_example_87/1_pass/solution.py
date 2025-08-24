import json
from collections import defaultdict

def build_adjacency(flights):
    adj = defaultdict(set)
    for a, b in flights:
        adj[a].add(b)
        adj[b].add(a)
    return adj

def find_hamiltonian_paths(cities, adjacency, start):
    cities_set = set(cities)
    paths = []

    def dfs(path, visited):
        if len(path) == len(cities):
            paths.append(path[:])
            return
        last = path[-1]
        for nxt in adjacency[last]:
            if nxt in visited or nxt not in cities_set:
                continue
            visited.add(nxt)
            path.append(nxt)
            dfs(path, visited)
            path.pop()
            visited.remove(nxt)

    dfs([start], set([start]))
    # Ensure each path includes all target cities exactly once
    return [p for p in paths if set(p) == cities_set and len(p) == len(cities)]

def compute_travel_days(order, durations, total_days):
    """
    For a linear order of cities [c0, c1, ..., c_{n-1}] with durations d_i,
    travel days t_k (k=0..n-2) are:
        t_k = sum_{i=0..k} d_i - k
    Feasibility requires sum(durations) - (n-1) == total_days.
    """
    n = len(order)
    d = [durations[c] for c in order]
    if sum(d) - (n - 1) != total_days:
        return None  # infeasible

    t = []
    cumulative = 0
    for k in range(n - 1):
        cumulative += d[k]
        t_k = cumulative - k
        t.append(t_k)

    # Validate travel days are strictly increasing and within [1, total_days]
    if not all(1 <= t_k <= total_days for t_k in t):
        return None
    if any(t[i] >= t[i + 1] for i in range(len(t) - 1)):
        return None

    # Validate city-day counts explicitly
    # City 0: days 1..t0
    # City i (1..n-2): days t_{i-1}..t_i
    # City n-1: days t_{n-2}..D
    presence = defaultdict(set)
    # City 0
    for day in range(1, t[0] + 1):
        presence[order[0]].add(day)
    # Middle cities
    for i in range(1, n - 1):
        start = t[i - 1]
        end = t[i] if i < n - 1 else total_days
        for day in range(start, end + 1):
            presence[order[i]].add(day)
    # Last city
    for day in range(t[-1], total_days + 1):
        presence[order[-1]].add(day)

    # Check counts
    for i, city in enumerate(order):
        if len(presence[city]) != durations[city]:
            return None

    return t

def build_itinerary(order, travel_days, total_days):
    """
    Construct day ranges per city:
      - City 0: Day 1 - t0
      - City i (1..n-2): Day t_{i-1} - t_i
      - City n-1: Day t_{n-2} - D
    """
    itinerary = []
    n = len(order)

    # City 0
    start = 1
    end = travel_days[0]
    itinerary.append({"day_range": f"Day {start}-{end}", "place": order[0]})

    # Middle cities
    for i in range(1, n - 1):
        start = travel_days[i - 1]
        end = travel_days[i]
        itinerary.append({"day_range": f"Day {start}-{end}", "place": order[i]})

    # Last city
    start = travel_days[-1]
    end = total_days
    itinerary.append({"day_range": f"Day {start}-{end}", "place": order[-1]})

    return itinerary

def main():
    # Inputs
    total_days = 7
    cities = ["Riga", "Amsterdam", "Mykonos"]
    desired_durations = {
        "Riga": 2,
        "Amsterdam": 2,
        "Mykonos": 5
    }
    # Direct flights (undirected)
    direct_flights = [
        ("Amsterdam", "Mykonos"),
        ("Riga", "Amsterdam")
    ]
    start_city = "Riga"
    require_riga_between_day1_day2 = True

    # Build adjacency
    adjacency = build_adjacency(direct_flights)

    # Find feasible orders (Hamiltonian paths) starting at Riga
    paths = find_hamiltonian_paths(cities, adjacency, start_city)

    best_itinerary = None

    for order in paths:
        # Ensure special constraint: in Riga on Day 1 and Day 2
        if require_riga_between_day1_day2 and (order[0] != "Riga" or desired_durations["Riga"] < 2):
            continue

        # Compute travel days
        t = compute_travel_days(order, desired_durations, total_days)
        if t is None:
            continue

        # Build itinerary
        itinerary = build_itinerary(order, t, total_days)

        # Final validation: ensure Riga covers Day 1 and Day 2
        if require_riga_between_day1_day2:
            # Riga is order[0] with range Day 1 - t0; must have t0 >= 2
            if t[0] < 2:
                continue

        best_itinerary = itinerary
        break

    if best_itinerary is None:
        output = {"itinerary": [], "note": "No feasible itinerary found with given constraints."}
    else:
        output = {"itinerary": best_itinerary}

    print(json.dumps(output, ensure_ascii=False))

if __name__ == "__main__":
    main()