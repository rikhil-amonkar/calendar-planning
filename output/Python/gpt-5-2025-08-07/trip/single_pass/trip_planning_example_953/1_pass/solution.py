import json
from collections import defaultdict

def build_adjacency(direct_flights):
    adj = defaultdict(set)
    for a, b in direct_flights:
        adj[a].add(b)
        adj[b].add(a)
    return adj

def find_hamiltonian_path(cities, adjacency, start_city, end_city):
    # Depth-first search with degree-ascending neighbor ordering and pruning
    n = len(cities)
    degrees = {c: len(adjacency[c]) for c in cities}

    # Sanity check: end city should be a leaf (or treated specially)
    # We enforce: do not visit end_city until last step
    def dfs(path, visited):
        if len(path) == n:
            return path if path[-1] == end_city else None

        current = path[-1]
        # Neighbors not yet visited
        candidates = [nb for nb in adjacency[current] if nb in cities and nb not in visited]
        # Do not take end_city unless it's the last step
        candidates = [nb for nb in candidates if not (nb == end_city and len(path) != n - 1)]
        # Degree-ascending heuristic to improve chances of success
        candidates.sort(key=lambda x: (degrees[x], x))

        for nb in candidates:
            visited.add(nb)
            path.append(nb)
            res = dfs(path, visited)
            if res:
                return res
            path.pop()
            visited.remove(nb)
        return None

    return dfs([start_city], {start_city})

def compute_itinerary(path, city_days, total_days, show_city=None, show_range=None):
    # Build itinerary with overlapping flight days:
    # For segment i>0, start_day equals previous end_day (flight day counted in both)
    itinerary_segments = []
    for i, city in enumerate(path):
        L = city_days[city]
        if i == 0:
            start = 1
        else:
            start = itinerary_segments[-1]['end_day']
        end = start + L - 1
        itinerary_segments.append({'place': city, 'start_day': start, 'end_day': end})

    # Validate total coverage equals total_days (end of last segment)
    if itinerary_segments[-1]['end_day'] != total_days:
        raise ValueError("Computed itinerary does not end on the required total_days.")

    # Validate each city's duration matches requested days
    for seg in itinerary_segments:
        dur = seg['end_day'] - seg['start_day'] + 1
        if dur != city_days[seg['place']]:
            raise ValueError(f"Duration mismatch for {seg['place']}.")

    # Validate show constraints
    if show_city and show_range:
        sr, er = show_range
        found = next((seg for seg in itinerary_segments if seg['place'] == show_city), None)
        if not found:
            raise ValueError("Show city not in itinerary.")
        if not (found['start_day'] <= sr and found['end_day'] >= er and found['start_day'] == 1):
            raise ValueError("Show days are not fully covered at the start of the trip in the show city.")

    return itinerary_segments

def main():
    # Inputs: trip constraints
    total_days = 18
    city_days = {
        "Salzburg": 4,
        "Stockholm": 2,
        "Venice": 5,
        "Frankfurt": 4,
        "Florence": 4,
        "Barcelona": 2,
        "Stuttgart": 3
    }
    # Direct flights (undirected edges)
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
        ("Venice", "Frankfurt"),
    ]

    show_city = "Venice"
    show_range = (1, 5)  # inclusive

    # Derived values and validations
    cities = list(city_days.keys())
    if show_city not in cities:
        raise ValueError("Show city is not in the city list.")

    # The trip should start in the show city to cover show days 1-5
    start_city = show_city

    # Identify mandatory endpoint constraints:
    # Salzburg only connects to Frankfurt, so it must be an endpoint in the path.
    end_city = "Salzburg"

    # Validate day arithmetic feasibility: sum(city_days) - (number_of_segments) should equal total_days - 1
    # Using e_n = 1 + sum(L_i) - n; We need e_n == total_days => sum(L_i) - n == total_days - 1
    total_required = sum(city_days.values())
    if total_required - len(cities) != total_days - 1:
        raise ValueError("Day totals are not compatible with overlaps and total trip length.")

    # Build adjacency
    adjacency = build_adjacency(direct_flights)
    # Ensure all cities appear in adjacency (even if degree 0)
    for c in cities:
        if c not in adjacency:
            adjacency[c] = set()

    # Find a Hamiltonian path that starts in Venice and ends in Salzburg using only direct flights
    path = find_hamiltonian_path(cities, adjacency, start_city, end_city)
    if not path:
        raise ValueError("No valid path found that satisfies the direct flight constraints and endpoint requirements.")

    # Build itinerary with overlapping flight days and validate show coverage
    segments = compute_itinerary(path, city_days, total_days, show_city=show_city, show_range=show_range)

    # Format final output
    itinerary = [
        {"day_range": f"Day {seg['start_day']}-{seg['end_day']}", "place": seg["place"]}
        for seg in segments
    ]

    print(json.dumps({"itinerary": itinerary}))

if __name__ == "__main__":
    main()