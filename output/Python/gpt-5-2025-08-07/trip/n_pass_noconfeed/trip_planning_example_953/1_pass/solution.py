import json
from collections import defaultdict

def build_graph(edges):
    graph = defaultdict(set)
    for a, b in edges:
        graph[a].add(b)
        graph[b].add(a)
    return graph

def find_hamiltonian_path(graph, start, nodes, must_end=None):
    nodes_set = set(nodes)
    degrees = {n: len(graph[n]) for n in nodes}

    def neighbor_order(nlist):
        # Sort neighbors by increasing degree (try to use constrained nodes earlier), but push must_end to the end
        return sorted(nlist, key=lambda x: (x == must_end, degrees[x]))

    path = [start]
    visited = {start}

    def dfs(current):
        if len(path) == len(nodes):
            if must_end is None or path[-1] == must_end:
                return True
            return False
        # Try neighbors that are in nodes set and not visited
        for nxt in neighbor_order([n for n in graph[current] if n in nodes_set and n not in visited]):
            # Avoid taking must_end too early (unless it's the final step)
            if must_end is not None and nxt == must_end and len(path) < len(nodes) - 1:
                continue
            visited.add(nxt)
            path.append(nxt)
            if dfs(nxt):
                return True
            path.pop()
            visited.remove(nxt)
        return False

    if dfs(start):
        return path
    return None

def compute_itinerary(path, durations, total_days, show_city=None, show_start=None, show_end=None):
    itinerary = []
    # Compute day ranges with overlap on flight days:
    # Each transition occurs on the last day of the current city's stay,
    # which is also the first day of the next city's stay.
    current_start = 1
    for i, city in enumerate(path):
        if i == 0:
            start_day = current_start
        else:
            # Overlap day (flight day) equals previous end day
            start_day = itinerary[-1]['end_day']
        end_day = start_day + durations[city] - 1
        itinerary.append({
            "place": city,
            "start_day": start_day,
            "end_day": end_day
        })
    # Validate total days
    if itinerary[-1]["end_day"] != total_days:
        raise ValueError(f"Total days mismatch: computed {itinerary[-1]['end_day']} vs expected {total_days}")
    # Validate show constraint
    if show_city:
        seg = next((x for x in itinerary if x["place"] == show_city), None)
        if not seg:
            raise ValueError(f"Show city {show_city} not in itinerary.")
        if not (seg["start_day"] <= show_start and seg["end_day"] >= show_end):
            raise ValueError(f"Show days {show_start}-{show_end} not fully within {show_city}'s stay {seg['start_day']}-{seg['end_day']}.")
    # Format final output as requested
    formatted = []
    for seg in itinerary:
        formatted.append({
            "day_range": f"Day {seg['start_day']}-{seg['end_day']}",
            "place": seg["place"]
        })
    return formatted

def main():
    # Input variables (constraints)
    total_days = 18
    desired_stays = {
        "Salzburg": 4,
        "Stockholm": 2,
        "Venice": 5,
        "Frankfurt": 4,
        "Florence": 4,
        "Barcelona": 2,
        "Stuttgart": 3
    }
    # Direct flight pairs (undirected)
    direct_flights = [
        ("Barcelona", "Frankfurt"),
        ("Florence", "Frankfurt"),
        ("Stockholm", "Barcelona"),
        ("Barcelona", "Florence"),
        ("Venice", "Barcelona"),
        ("Stuttgart", "Barcelona"),
        ("Frankfurt", "Salzburg"),
        ("Stockholm", "Frankfurt"),
        ("Stuttgart", "Stockholm"),
        ("Stuttgart", "Frankfurt"),
        ("Venice", "Stuttgart"),
        ("Venice", "Frankfurt")
    ]
    show_city = "Venice"
    show_start_day = 1
    show_end_day = 5

    cities = list(desired_stays.keys())
    graph = build_graph(direct_flights)

    # Validate graph contains all cities
    for c in cities:
        if c not in graph:
            graph[c] = set()

    # Compute minimal flights needed assuming each city is visited once
    min_flights = len(cities) - 1
    # Check sum of durations equals total_days + min_flights (to use flight-day overlaps)
    sum_durations = sum(desired_stays.values())
    if sum_durations != total_days + min_flights:
        raise ValueError(f"Infeasible durations: sum={sum_durations}, total_days={total_days}, flights_needed={min_flights}")

    # Determine degree-1 nodes that must be endpoints (except the start city if it has degree 1)
    deg1_nodes = [c for c in cities if len(graph[c]) == 1]
    must_end = None
    for n in deg1_nodes:
        if n != show_city:
            must_end = n
            break

    # Find a Hamiltonian path starting at the show city and ending at the degree-1 node if applicable
    path = find_hamiltonian_path(graph, show_city, cities, must_end=must_end)
    if not path:
        raise ValueError("No feasible Hamiltonian path found with direct flights and constraints.")

    # Compute itinerary with overlapping flight days
    itinerary = compute_itinerary(
        path,
        desired_stays,
        total_days,
        show_city=show_city,
        show_start=show_start_day,
        show_end=show_end_day
    )

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()