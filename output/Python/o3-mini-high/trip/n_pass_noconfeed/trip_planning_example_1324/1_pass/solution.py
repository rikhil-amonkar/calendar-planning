import json

# Trip parameters
durations = {
    "Venice": 4,
    "Barcelona": 3,
    "Copenhagen": 4,
    "Lyon": 4,
    "Reykjavik": 4,
    "Dubrovnik": 5,
    "Athens": 2,
    "Tallinn": 5,
    "Munich": 3
}

# Special time-window constraints:
# For a city visited from start_day to end_day (inclusive),
# - Barcelona must include at least one day between 10 and 12 (i.e. start <= 12 and end >= 10)
# - Copenhagen must include at least one day between 7 and 10 (i.e. start <= 10 and end >= 7)
# - Dubrovnik must include at least one day between 16 and 20 (i.e. start <= 20 and end >= 16)
special_constraints = {
    "Barcelona": {"min_end": 10, "max_start": 12},
    "Copenhagen": {"min_end": 7, "max_start": 10},
    "Dubrovnik": {"min_end": 16, "max_start": 20},
}

# Build the flight network (graph) of direct flights.
# Most flights are bidirectional except "Reykjavik to Athens" which is one-way.
def build_flight_graph():
    cities = list(durations.keys())
    graph = {city: set() for city in cities}
    # Each tuple: (CityA, CityB, directed)
    # If directed is True, flight is only available from CityA -> CityB.
    flights = [
        ("Copenhagen", "Athens", False),
        ("Copenhagen", "Dubrovnik", False),
        ("Munich", "Tallinn", False),
        ("Copenhagen", "Munich", False),
        ("Venice", "Munich", False),
        ("Reykjavik", "Athens", True),  # one-way from Reykjavik -> Athens
        ("Athens", "Dubrovnik", False),
        ("Venice", "Athens", False),
        ("Lyon", "Barcelona", False),
        ("Copenhagen", "Reykjavik", False),
        ("Reykjavik", "Munich", False),
        ("Athens", "Munich", False),
        ("Lyon", "Munich", False),
        ("Barcelona", "Reykjavik", False),
        ("Venice", "Copenhagen", False),
        ("Barcelona", "Dubrovnik", False),
        ("Lyon", "Venice", False),
        ("Dubrovnik", "Munich", False),
        ("Barcelona", "Athens", False),
        ("Copenhagen", "Barcelona", False),
        ("Venice", "Barcelona", False),
        ("Barcelona", "Munich", False),
        ("Barcelona", "Tallinn", False),
        ("Copenhagen", "Tallinn", False)
    ]
    for frm, to, directed in flights:
        # Always add flight from frm to to.
        graph[frm].add(to)
        if not directed:
            graph[to].add(frm)
    return graph

# Check if a special time-window constraint is satisfied for a city given its start and end day.
def check_time_constraint(city, start, end):
    if city in special_constraints:
        constraint = special_constraints[city]
        # For constraint: start must be <= max_start and end must be >= min_end.
        if start > constraint["max_start"] or end < constraint["min_end"]:
            return False
    return True

# Recursive backtracking search for a valid itinerary.
def search_itinerary(path, current_end, visited, itinerary, graph, total_cities):
    if len(path) == total_cities:
        # When all cities are visited, current_end should be 26 days.
        if current_end == 26:
            return itinerary.copy()
        else:
            return None

    for city in durations:
        if city in visited:
            continue
        # If already have a city in the path, check flight connectivity from the last city.
        if path:
            last_city = path[-1]
            if city not in graph[last_city]:
                continue

        # For the first city, its start day is 1.
        candidate_start = current_end if path else 1
        candidate_end = candidate_start + durations[city] - 1

        # Check special constraints for cities that have time-window events.
        if not check_time_constraint(city, candidate_start, candidate_end):
            continue

        # Choose the city.
        visited.add(city)
        path.append(city)
        itinerary.append({"day_range": f"Day {candidate_start}-{candidate_end}", "place": city})

        # Next city's start day will be the current candidate's end day.
        result = search_itinerary(path, candidate_end, visited, itinerary, graph, total_cities)
        if result is not None:
            return result

        # Backtrack.
        visited.remove(city)
        path.pop()
        itinerary.pop()

    return None

def main():
    graph = build_flight_graph()
    total_cities = len(durations)  # should be 9
    solution = search_itinerary([], 0, set(), [], graph, total_cities)
    if solution is None:
        output = {"itinerary": []}
    else:
        output = {"itinerary": solution}
    print(json.dumps(output, indent=2))

if __name__ == '__main__':
    main()