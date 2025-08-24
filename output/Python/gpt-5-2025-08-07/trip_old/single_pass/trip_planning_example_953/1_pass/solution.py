import json

def build_graph(flight_pairs):
    graph = {}
    for a, b in flight_pairs:
        graph.setdefault(a, set()).add(b)
        graph.setdefault(b, set()).add(a)
    return graph

def find_hamiltonian_path(graph, start, end, require_penultimate=None, nodes=None):
    if nodes is None:
        nodes = list(graph.keys())
    n = len(nodes)
    visited = set([start])
    path = [start]

    def dfs(current):
        if len(path) == n:
            if path[-1] == end and (require_penultimate is None or path[-2] == require_penultimate):
                return path.copy()
            return None

        # Prefer neighbors with smaller degree to reduce dead-ends
        neighbors = sorted(graph[current], key=lambda x: len(graph[x]))
        for nb in neighbors:
            if nb in visited:
                continue
            # Do not go to 'end' before the last step
            if nb == end and len(path) != n - 1:
                continue
            # If the final move is to be made, ensure current is the required penultimate (if specified)
            if len(path) == n - 1 and nb == end and require_penultimate is not None and current != require_penultimate:
                continue

            visited.add(nb)
            path.append(nb)
            res = dfs(nb)
            if res:
                return res
            path.pop()
            visited.remove(nb)
        return None

    return dfs(start)

def schedule_itinerary(path, durations, total_days, show_city, show_start, show_end):
    # Determine overlap counts: 1 for endpoints, 2 for interior cities
    overlaps = {}
    for i, city in enumerate(path):
        if i == 0 or i == len(path) - 1:
            overlaps[city] = 1
        else:
            overlaps[city] = 2

    # Calculate internal (non-overlap) days per city
    internal_days = {city: durations[city] - overlaps[city] for city in path}
    if any(v < 0 for v in internal_days.values()):
        raise ValueError("Negative internal days required by constraints; unsatisfiable.")

    # Verify total calendar days align: sum(durations) - (number of flights) == total_days
    number_of_flights = len(path) - 1
    if sum(durations.values()) - number_of_flights != total_days:
        raise ValueError("Total days do not align with overlaps and durations.")

    # First city must be show_city and its show range must align
    if path[0] != show_city:
        raise ValueError("Show city must be the starting city to honor day-locked attendance.")
    if durations[show_city] != (show_end - show_start + 1):
        raise ValueError("Show city duration must match the day-locked attendance window.")

    # Assign day ranges with overlaps on transition days
    start_day = {}
    end_day = {}

    # First city: occupies show_start..show_end (with right overlap on show_end)
    first = path[0]
    start_day[first] = show_start
    end_day[first] = show_end  # boundary/flight day to next city occurs on show_end

    # Interior cities up to penultimate
    current_day = end_day[first] + 1  # first pure day after the first boundary day
    for i in range(1, len(path) - 1):
        city = path[i]
        left_boundary = end_day[path[i - 1]]  # same as previous city's end (overlap)
        p = internal_days[city]
        start_day[city] = left_boundary
        end_day[city] = start_day[city] + p + 1  # +1 for right boundary overlap
        current_day = end_day[city] + 1

    # Last city: no right boundary; only left boundary + internal days
    last = path[-1]
    p_last = internal_days[last]
    start_day[last] = end_day[path[-2]]
    end_day[last] = start_day[last] + p_last

    # Validate calendar coverage ends at total_days
    if end_day[last] != total_days:
        raise ValueError("Scheduled itinerary does not end on the desired total day count.")

    # Validate direct flights exist on each boundary day
    for i in range(len(path) - 1):
        a, b = path[i], path[i + 1]
        # Flight happens on end_day[a] == start_day[b]
        if b not in graph[a]:
            raise ValueError(f"No direct flight between {a} and {b}.")

    # Validate durations by counting days per city (including overlaps)
    def days_for_city(c):
        return set(range(start_day[c], end_day[c] + 1))

    for c in path:
        if len(days_for_city(c)) != durations[c]:
            raise ValueError(f"Duration mismatch for {c}.")

    # Validate show city coverage
    show_days = set(range(show_start, show_end + 1))
    if not show_days.issubset(days_for_city(show_city)):
        raise ValueError("Show days not fully covered in show city.")

    # Build itinerary output
    itinerary = []
    for c in path:
        itinerary.append({
            "day_range": f"Day {start_day[c]}-{end_day[c]}",
            "place": c
        })
    return itinerary

# Input variables based on the given trip constraints
total_days = 18
durations = {
    "Salzburg": 4,
    "Stockholm": 2,
    "Venice": 5,
    "Frankfurt": 4,
    "Florence": 4,
    "Barcelona": 2,
    "Stuttgart": 3
}
cities = ["Venice", "Stuttgart", "Stockholm", "Barcelona", "Florence", "Frankfurt", "Salzburg"]

flight_pairs = [
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

graph = build_graph(flight_pairs)

start_city = "Venice"
end_city = "Salzburg"
require_penultimate = "Frankfurt"  # To ensure Salzburg is reachable (only via Frankfurt)

show_city = "Venice"
show_start = 1
show_end = 5

# Compute a valid path
path = find_hamiltonian_path(graph, start=start_city, end=end_city, require_penultimate=require_penultimate, nodes=cities)
if not path:
    raise RuntimeError("Failed to compute a valid city sequence under direct flight constraints.")

# Schedule days honoring overlaps and the show constraint
itinerary = schedule_itinerary(path, durations, total_days, show_city, show_start, show_end)

# Output JSON
print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))