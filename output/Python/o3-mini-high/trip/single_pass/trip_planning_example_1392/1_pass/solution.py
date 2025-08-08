#!/usr/bin/env python3
import json

# Define the flight connections (bidirectional)
flights = [
    ("Venice", "Nice"),
    ("Naples", "Amsterdam"),
    ("Barcelona", "Nice"),
    ("Amsterdam", "Nice"),
    ("Stuttgart", "Valencia"),
    ("Stuttgart", "Porto"),
    ("Split", "Stuttgart"),
    ("Split", "Naples"),
    ("Valencia", "Amsterdam"),
    ("Barcelona", "Porto"),
    ("Valencia", "Naples"),
    ("Venice", "Amsterdam"),
    ("Barcelona", "Naples"),
    ("Barcelona", "Valencia"),
    ("Split", "Amsterdam"),
    ("Barcelona", "Venice"),
    ("Stuttgart", "Amsterdam"),
    ("Naples", "Nice"),
    ("Venice", "Stuttgart"),
    ("Split", "Barcelona"),
    ("Porto", "Nice"),
    ("Barcelona", "Stuttgart"),
    ("Venice", "Naples"),
    ("Porto", "Amsterdam"),
    ("Porto", "Valencia"),
    ("Stuttgart", "Naples"),
    ("Barcelona", "Amsterdam")
]

# Build graph (each city -> set of cities with direct flights)
graph = {}
def add_edge(a, b):
    graph.setdefault(a, set()).add(b)
    graph.setdefault(b, set()).add(a)

for a, b in flights:
    add_edge(a, b)

# List of cities with required durations and any event windows.
# The order here is chosen to favor a candidate itinerary.
# Each city has a "duration" (number of days to be spent, counting the flight day overlap)
# and optionally an "events" dict. For each event, the value is a tuple (window_start, window_end).
#
# Special note for Venice: The conference requires that both day 6 and day 10 are included,
# so we will enforce: segment_start <= 6 and segment_end >= 10.
cities_info = {
    # Order chosen: Valencia, Barcelona, Venice, Amsterdam, Split, Naples, Stuttgart, Porto, Nice
    "Valencia": {"duration": 5, "events": {}},
    "Barcelona": {"duration": 2, "events": {"workshop": (5, 6)}},  # Workshop must occur between day 5 and day6.
    "Venice": {"duration": 5, "events": {"conference": (6, 10)}},   # Conference: must cover day6 and day10.
    "Amsterdam": {"duration": 4, "events": {}},
    "Split": {"duration": 5, "events": {}},
    "Naples": {"duration": 3, "events": {"friend_meeting": (18, 20)}},  # Friend meeting in Naples between day18-20.
    "Stuttgart": {"duration": 2, "events": {}},
    "Porto": {"duration": 4, "events": {}},
    "Nice": {"duration": 2, "events": {"friend_meeting": (23, 24)}}      # Meet friends in Nice between day23-24.
}

# List of all cities in the desired order (the DFS will iterate over this list order)
city_list = list(cities_info.keys())

# DFS search to build an itinerary.
# The itinerary will be a list of tuples: (city, seg_start, seg_end)
# where the segment for a city is defined as starting at seg_start and ending at seg_end.
#
# The rule is: 
#   - The first city starts at day 1.
#   - If a city has a required duration d, its segment is [current_day, current_day + d - 1].
#   - Then, when flying from one city to the next on day X (which is the end day of the previous segment),
#     that day (X) counts for both cities.
#
# We also prune if the partial assignment cannot lead to a complete itinerary of 24 unique days.
def dfs(route, current_day, remaining):
    # When no remaining city, check if end day equals 24.
    if not remaining:
        if current_day == 24:
            return route
        else:
            return None

    # Prune: if the final day computed from current_day and remaining durations does not equal 24.
    sum_remaining = sum(cities_info[city]['duration'] for city in remaining)
    if current_day + (sum_remaining - len(remaining)) != 24:
        return None

    # Iterate over remaining cities in the given order.
    for i, city in enumerate(remaining):
        # If not the very first city, check that there is a direct flight from the last city in the route.
        if route:
            last_city = route[-1][0]
            if city not in graph.get(last_city, set()):
                continue

        duration = cities_info[city]['duration']
        seg_start = current_day
        seg_end = current_day + duration - 1
        if seg_end > 24:
            continue

        # Check event constraints in the city.
        valid = True
        for event, window in cities_info[city].get("events", {}).items():
            # For Venice conference, require that the segment covers both day 6 and day 10.
            if city == "Venice" and event == "conference":
                if not (seg_start <= 6 and seg_end >= 10):
                    valid = False
                    break
            else:
                # For other events, require an intersection of the segment [seg_start, seg_end] and the event window.
                window_start, window_end = window
                # Check if the segment and the event window intersect.
                if seg_end < window_start or seg_start > window_end:
                    valid = False
                    break
        if not valid:
            continue

        new_current = seg_end  # Next city starts on the same day as the current city's end (flight day overlap)
        new_route = route + [(city, seg_start, seg_end)]
        # Create a new list for remaining cities (remove the current candidate)
        new_remaining = remaining[:i] + remaining[i+1:]
        result = dfs(new_route, new_current, new_remaining)
        if result is not None:
            return result
    return None

def main():
    # Start DFS with an empty route and starting day 1.
    itinerary_route = dfs([], 1, city_list)
    if itinerary_route is None:
        output = {"itinerary": []}
    else:
        # Format itinerary into the required JSON structure.
        itinerary = []
        for seg in itinerary_route:
            city, start, end = seg
            # Build day range string.
            day_range = f"Day {start}-{end}"
            itinerary.append({"day_range": day_range, "place": city})
        output = {"itinerary": itinerary}
    print(json.dumps(output))

if __name__ == '__main__':
    main()