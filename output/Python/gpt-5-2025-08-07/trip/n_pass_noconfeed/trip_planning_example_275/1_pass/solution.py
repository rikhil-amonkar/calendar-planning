import json

def build_graph(direct_connections):
    graph = {}
    for a, b in direct_connections:
        graph.setdefault(a, set()).add(b)
        graph.setdefault(b, set()).add(a)
    return graph

def find_hamiltonian_path_ending_at(graph, cities, end_city):
    n = len(cities)
    city_set = set(cities)

    # Start candidates: all cities except end_city. Prefer degree-1 nodes for efficiency.
    degrees = {c: len(graph.get(c, [])) for c in cities}
    start_candidates = sorted([c for c in cities if c != end_city], key=lambda c: (degrees[c], c))

    def dfs(path, visited):
        if len(path) == n:
            if path[-1] == end_city:
                return path
            return None
        last = path[-1]
        for nxt in sorted(graph.get(last, [])):
            if nxt in city_set and nxt not in visited:
                visited.add(nxt)
                result = dfs(path + [nxt], visited)
                if result:
                    return result
                visited.remove(nxt)
        return None

    for start in start_candidates:
        res = dfs([start], {start})
        if res:
            return res
    return None

def compute_itinerary(path, desired_stays, total_days, required_presence=None):
    # Validate sum of desired stays matches total_days + number_of_flights (overlaps on flight days)
    sum_desired = sum(desired_stays[c] for c in path)
    required_sum = total_days + (len(path) - 1)
    if sum_desired != required_sum:
        raise ValueError(f"Infeasible durations: sum(desired)={sum_desired} must equal total_days + flights={required_sum}")

    # Ensure required presence constraint is set
    if required_presence is None:
        required_presence = {}

    # Determine last city and its start day
    last_city = path[-1]
    l_last = desired_stays[last_city]
    start_last = total_days - l_last + 1

    # Check required presence days are within last city segment
    if last_city in required_presence:
        for d in required_presence[last_city]:
            if not (start_last <= d <= total_days):
                raise ValueError(f"Required presence day {d} not within {last_city} stay {start_last}-{total_days}")

    # Back-calculate start days for each segment (inclusive, with overlap on flight days)
    starts = [None] * len(path)
    starts[-1] = start_last
    for i in range(len(path)-2, -1, -1):
        city = path[i]
        l = desired_stays[city]
        starts[i] = starts[i+1] - l + 1

    # Validate that the first city starts on day 1
    if starts[0] != 1:
        # Attempt to shift if possible (should not be necessary if sums are consistent)
        shift = 1 - starts[0]
        starts = [s + shift for s in starts]
        if starts[0] != 1 or starts[-1] > total_days:
            raise ValueError("Computed schedule does not align to Day 1 start.")

    # Construct itinerary with overlapping day at each flight (shared day counts for both cities)
    itinerary = []
    for i, city in enumerate(path):
        start = starts[i]
        end = starts[i+1] if i < len(path) - 1 else total_days
        # Additional guard: ensure increasing non-decreasing order
        if start < 1 or end > total_days or start > end:
            raise ValueError(f"Invalid segment for {city}: Day {start}-{end}")
        itinerary.append({"day_range": f"Day {start}-{end}", "place": city})

    return itinerary

def main():
    # Input variables based on the provided constraints
    total_days = 14
    cities = ["Vilnius", "Split", "Madrid", "Santorini"]
    desired_stays = {
        "Split": 5,
        "Vilnius": 4,
        "Santorini": 2,
        "Madrid": 6
    }
    direct_connections = [
        ("Vilnius", "Split"),
        ("Split", "Madrid"),
        ("Madrid", "Santorini")
    ]
    # Required presence: conference in Santorini on days 13 and 14
    required_presence = {"Santorini": [13, 14]}

    # Build graph and find a valid path that ends in Santorini
    graph = build_graph(direct_connections)
    end_city = "Santorini"
    path = find_hamiltonian_path_ending_at(graph, cities, end_city)
    if not path:
        raise RuntimeError("No valid city visitation path found that ends in Santorini with direct flights only.")

    # Compute itinerary
    itinerary = compute_itinerary(path, desired_stays, total_days, required_presence)

    # Output as JSON
    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()