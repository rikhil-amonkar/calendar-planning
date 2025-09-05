#!/usr/bin/env python3
import json
import sys

# Define the cities with their required durations (in days)
cities = {
    "Stockholm": 3,
    "Amsterdam": 3,
    "Valencia": 2,
    "Vienna": 5,
    "Athens": 5,
    "Reykjavik": 5,
    "Bucharest": 3,
    "Riga": 3,
    "Frankfurt": 4,
    "Salzburg": 5
}

# Event constraints: Each event city must have at least one day in the given window.
# Format: city: (min_day, max_day)
event_windows = {
    "Stockholm": (1, 3),   # meet friend between day 1 and 3
    "Valencia": (5, 6),    # annual show in Valencia from day 5 to 6
    "Vienna": (6, 10),     # wedding in Vienna between day 6 and 10
    "Athens": (14, 18),    # workshop in Athens between day 14 and 18
    "Riga": (18, 20)       # conference in Riga between day 18 and 20
}

# Build the flight connectivity graph.
# For flights specified as "A and B", we add bidirectional edges.
# For flights specified as "from A to B", we add a directed edge A->B only.
def build_flight_graph():
    graph = {city: set() for city in cities}
    def add_bidirectional(a, b):
        graph[a].add(b)
        graph[b].add(a)
    def add_directional(a, b):
        graph[a].add(b)
    
    # According to the given list:
    add_bidirectional("Valencia", "Frankfurt")
    add_bidirectional("Vienna", "Bucharest")
    add_directional("Valencia", "Athens")            # from Valencia to Athens
    add_bidirectional("Athens", "Bucharest")
    add_bidirectional("Riga", "Frankfurt")
    add_bidirectional("Stockholm", "Athens")
    add_bidirectional("Amsterdam", "Bucharest")
    add_directional("Athens", "Riga")                 # from Athens to Riga
    add_bidirectional("Amsterdam", "Frankfurt")
    add_bidirectional("Stockholm", "Amsterdam")
    add_bidirectional("Amsterdam", "Valencia")
    add_bidirectional("Vienna", "Frankfurt")
    add_bidirectional("Valencia", "Bucharest")
    add_bidirectional("Bucharest", "Frankfurt")
    add_bidirectional("Stockholm", "Frankfurt")
    add_bidirectional("Valencia", "Vienna")
    add_directional("Reykjavik", "Athens")            # from Reykjavik to Athens
    add_bidirectional("Frankfurt", "Salzburg")
    add_bidirectional("Amsterdam", "Vienna")
    add_bidirectional("Stockholm", "Reykjavik")
    add_bidirectional("Amsterdam", "Riga")
    add_bidirectional("Stockholm", "Riga")
    add_bidirectional("Vienna", "Reykjavik")
    add_bidirectional("Amsterdam", "Athens")
    add_bidirectional("Athens", "Frankfurt")
    add_bidirectional("Vienna", "Athens")
    add_bidirectional("Riga", "Bucharest")
    
    return graph

flight_graph = build_flight_graph()

# Compute the timeline for a given route.
# Using the rule: The first city is visited starting day 1 and occupies its full duration.
# For each subsequent city, if the traveler flies on day X then that day counts for both cities.
# So if city i has duration d, its visit covers days [start, start + d - 1], and the next city starts on the same day as city i's end.
def compute_timeline(route, durations):
    timeline = []
    day = 1
    for city in route:
        start = day
        finish = day + durations[city] - 1
        timeline.append((city, start, finish))
        day = finish  # next city starts on the finishing day (overlap flight day)
    return timeline

# Check if the visit for an event city overlaps its required window.
def check_event_constraints(timeline, event_windows):
    for city, start, finish in timeline:
        if city in event_windows:
            wmin, wmax = event_windows[city]
            # There must be at least one day in the visit that is between wmin and wmax (inclusive).
            # That is, the intervals [start, finish] and [wmin, wmax] must intersect.
            if finish < wmin or start > wmax:
                return False
    return True

# Backtracking search for a valid itinerary.
def search_itinerary(current_route, remaining, durations, event_windows, flight_graph):
    # If route is complete, check overall timeline and return if valid.
    if not remaining:
        timeline = compute_timeline(current_route, durations)
        # Total trip days = sum(durations) - (len(route) - 1) must be 29.
        total_days = sum(durations[city] for city in current_route) - (len(current_route) - 1)
        if total_days == 29 and check_event_constraints(timeline, event_windows):
            return timeline
        else:
            return None
    # Try each possible next city.
    last_city = current_route[-1] if current_route else None
    for city in list(remaining):
        # Enforce that the very first city is Stockholm.
        if not current_route and city != "Stockholm":
            continue
        # If there is a last city, check that a direct flight exists
        if last_city and city not in flight_graph[last_city]:
            continue
        # Extend the route and check partial timeline constraints.
        new_route = current_route + [city]
        timeline = compute_timeline(new_route, durations)
        valid_so_far = True
        # For each city already visited that has an event, ensure its visit interval
        # does intersect its event window. (We do not prune too strictly because later days may shift slightly,
        # but the timeline is fully determined by the route order.)
        for c, s, f in timeline:
            if c in event_windows:
                wmin, wmax = event_windows[c]
                if f < wmin or s > wmax:
                    valid_so_far = False
                    break
        if not valid_so_far:
            continue

        new_remaining = remaining.copy()
        new_remaining.remove(city)
        result = search_itinerary(new_route, new_remaining, durations, event_windows, flight_graph)
        if result is not None:
            return result
    return None

def main():
    all_cities = set(cities.keys())
    timeline = search_itinerary([], all_cities, cities, event_windows, flight_graph)
    if timeline is None:
        # No valid itinerary was found.
        output = {"itinerary": []}
    else:
        # Build the itinerary list as required.
        itinerary = []
        for city, start, finish in timeline:
            day_range = f"Day {start}-{finish}"
            itinerary.append({"day_range": day_range, "place": city})
        output = {"itinerary": itinerary}
    # Print JSON output.
    print(json.dumps(output, indent=2))

if __name__ == '__main__':
    main()