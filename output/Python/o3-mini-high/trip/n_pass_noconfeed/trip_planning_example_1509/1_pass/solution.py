import json

def build_flight_graph():
    # List of direct flights (treating all as bidirectional)
    flights = [
        ("Warsaw", "Riga"),
        ("Warsaw", "Tallinn"),
        ("Copenhagen", "Helsinki"),
        ("Lyon", "Paris"),
        ("Copenhagen", "Warsaw"),
        ("Lyon", "Oslo"),
        ("Paris", "Oslo"),
        ("Paris", "Riga"),
        ("Krakow", "Helsinki"),
        ("Paris", "Tallinn"),
        ("Oslo", "Riga"),
        ("Krakow", "Warsaw"),
        ("Paris", "Helsinki"),
        ("Copenhagen", "Santorini"),
        ("Helsinki", "Warsaw"),
        ("Helsinki", "Riga"),
        ("Copenhagen", "Riga"),
        ("Paris", "Krakow"),
        ("Copenhagen", "Oslo"),
        ("Oslo", "Tallinn"),
        ("Oslo", "Helsinki"),
        ("Copenhagen", "Tallinn"),
        ("Oslo", "Krakow"),
        ("Riga", "Tallinn"),   # from Riga to Tallinn
        ("Helsinki", "Tallinn"),
        ("Paris", "Copenhagen"),
        ("Paris", "Warsaw"),
        ("Santorini", "Oslo"),  # from Santorini to Oslo
        ("Oslo", "Warsaw")
    ]
    # All cities list (10 European cities to be visited)
    cities = ["Lyon", "Paris", "Tallinn", "Copenhagen", "Santorini", "Oslo", "Krakow", "Warsaw", "Helsinki", "Riga"]
    graph = {city: set() for city in cities}
    for a, b in flights:
        if a in graph and b in graph:
            graph[a].add(b)
            graph[b].add(a)
        else:
            if a not in graph:
                graph[a] = {b}
            else:
                graph[a].add(b)
            if b not in graph:
                graph[b] = {a}
            else:
                graph[b].add(a)
    return graph

# Required durations (in days) for each city's visit.
durations = {
    "Paris": 5,
    "Warsaw": 2,
    "Krakow": 2,
    "Tallinn": 2,
    "Riga": 2,
    "Copenhagen": 5,
    "Helsinki": 5,
    "Oslo": 5,
    "Santorini": 2,
    "Lyon": 4
}

# Event constraints (city: (event_start_day, event_end_day))
# They require that the city's scheduled stay (which is a day-range computed from the itinerary order)
# must overlap with the given event window.
event_constraints = {
    "Paris": (4, 8),         # Meet friends in Paris between day 4 and day 8
    "Krakow": (17, 18),      # Workshop in Krakow between day 17 and day 18
    "Helsinki": (18, 22),    # Meet a friend in Helsinki between day 18 and day 22
    "Santorini": (12, 13),   # Visit relatives in Santorini between day 12 and day 13
    "Riga": (23, 24)         # Wedding in Riga between day 23 and day 24
}

# The list of cities in a preferred order to guide our search.
cities_list = ["Lyon", "Paris", "Tallinn", "Copenhagen", "Santorini", "Oslo", "Krakow", "Warsaw", "Helsinki", "Riga"]

flight_graph = build_flight_graph()

# Backtracking function to find an ordering that satisfies flight connectivity and event time windows.
def backtrack(path, current_day):
    # If a complete itinerary has been found:
    if len(path) == len(cities_list):
        return path
    for city in cities_list:
        if city in path:
            continue
        # For non-first cities, ensure a direct flight exists from the previous city.
        if path:
            last_city = path[-1]
            if city not in flight_graph[last_city]:
                continue
        # Determine the start and end days for the candidate city's stay.
        start_day = current_day
        end_day = start_day + durations[city] - 1
        # If the city has an event, its stay must overlap with the event window.
        if city in event_constraints:
            event_start, event_end = event_constraints[city]
            if start_day > event_end or end_day < event_start:
                continue
        # The next city's start day is the end_day (flight day overlap counts for both cities).
        new_current_day = end_day
        result = backtrack(path + [city], new_current_day)
        if result is not None:
            return result
    return None

solution = backtrack([], 1)

# Using the solution ordering, compute the itinerary day ranges.
itinerary = []
if solution:
    current_day = 1
    for city in solution:
        end_day = current_day + durations[city] - 1
        itinerary.append({"day_range": f"Day {current_day}-{end_day}", "place": city})
        # Next city's start day is the same as the current segment's end day (flight day overlap).
        current_day = end_day
else:
    itinerary = []

# Output the itinerary as a JSON-formatted dictionary.
print(json.dumps({"itinerary": itinerary}))
if __name__ == "__main__":
    pass