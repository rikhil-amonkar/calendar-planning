import json

def build_adjacency(edges):
    adj = {}
    for a, b in edges:
        adj.setdefault(a, set()).add(b)
        adj.setdefault(b, set()).add(a)
    return adj

def find_hamiltonian_path(start, nodes, adj):
    path = [start]
    visited = set([start])

    def backtrack(curr):
        if len(path) == len(nodes):
            return path.copy()
        for nxt in adj.get(curr, []):
            if nxt in visited:
                continue
            path.append(nxt)
            visited.add(nxt)
            res = backtrack(nxt)
            if res is not None:
                return res
            path.pop()
            visited.remove(nxt)
        return None

    return backtrack(start)

def compute_itinerary(total_days, cities, desired_durations, direct_flights, conference_city, conference_days):
    # Build adjacency
    adj = build_adjacency(direct_flights)

    # Ensure all cities are present in adjacency
    for c in cities:
        adj.setdefault(c, set())

    # Find a path that starts at the conference city and visits all cities using direct flights only
    route = find_hamiltonian_path(conference_city, cities, adj)
    if route is None:
        raise ValueError("No valid route visiting all cities with direct flights only starting from the conference city.")

    # Validate total durations vs total days + flights (overlap on each flight day counts in both cities)
    flights = len(route) - 1
    if sum(desired_durations[c] for c in route) != total_days + flights:
        raise ValueError("Desired durations are inconsistent with total days and number of flights (overlap days).")

    # Compute flight days so that durations match, considering overlap-on-flight-day rule
    # Let city0 cover days [1, d1], city1 cover [d1, d2], city2 cover [d2, total_days]
    city0, city1, city2 = route
    d1 = desired_durations[city0]  # Flight from city0 to city1 on day d1
    d2 = d1 + desired_durations[city1] - 1  # Flight from city1 to city2 on day d2

    # Validate last city's duration
    if desired_durations[city2] != total_days - d2 + 1:
        raise ValueError("Durations do not align with total days when applying overlap rule.")

    # Validate conference days are covered in the conference city
    if conference_city != city0:
        raise ValueError("Conference city must be the starting city to satisfy day presence.")
    if not conference_days or max(conference_days) > d1:
        # Must be in the conference city on all conference days, which are within [1, d1]
        pass  # they are; since d1 >= max(conference_days) is required
    if max(conference_days) > d1:
        raise ValueError("Conference days are not fully covered in the conference city.")

    # Validate direct flights exist along route
    for a, b in zip(route, route[1:]):
        if b not in adj.get(a, set()):
            raise ValueError(f"No direct flight between {a} and {b}.")

    itinerary = [
        {"day_range": f"Day 1-{d1}", "place": city0},
        {"day_range": f"Day {d1}-{d2}", "place": city1},
        {"day_range": f"Day {d2}-{total_days}", "place": city2},
    ]
    return {"itinerary": itinerary}

if __name__ == "__main__":
    # Input variables (trip constraints)
    total_days = 12
    cities = ["Brussels", "Barcelona", "Split"]
    desired_durations = {
        "Brussels": 2,
        "Barcelona": 7,
        "Split": 5
    }
    conference_city = "Brussels"
    conference_days = [1, 2]  # Must be in Brussels on these days
    direct_flights = {
        ("Brussels", "Barcelona"),
        ("Barcelona", "Split")
    }

    result = compute_itinerary(
        total_days=total_days,
        cities=cities,
        desired_durations=desired_durations,
        direct_flights=direct_flights,
        conference_city=conference_city,
        conference_days=conference_days
    )
    print(json.dumps(result))