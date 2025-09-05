import json
import itertools

# Input variables: total trip days and required days per city
total_days = 8
city_durations = {
    "Prague": 4,
    "Stuttgart": 2,
    "Split": 2,
    "Krakow": 2,
    "Florence": 2
}

# Event constraints:
# For Stuttgart: attend a wedding between day 2 and day 3.
# For Split: meet friends between day 3 and day 4.
# These constraints require that the city’s visit spans an interval that covers
# the given window. For a city visited not first, its interval is defined as:
# [departure_day(previous city), departure_day(this city)]
events = {
    "Stuttgart": {"window": (2, 3)},
    "Split": {"window": (3, 4)}
}

# List of cities (we must visit all these exactly once)
cities = list(city_durations.keys())

# Direct flights are given as pairs (bidirectional)
flights_list = [
    ("Stuttgart", "Split"),
    ("Prague", "Florence"),
    ("Krakow", "Stuttgart"),
    ("Krakow", "Split"),
    ("Split", "Prague"),
    ("Krakow", "Prague")
]

# Build a graph for direct flight connectivity (bidirectional)
flight_graph = {city: set() for city in cities}
for a, b in flights_list:
    flight_graph[a].add(b)
    flight_graph[b].add(a)

def compute_departure_days(order):
    """
    Given an order (list of cities), compute the departure day for each city.
    For the first city, departure day = duration.
    For subsequent cities, departure_day[i] = departure_day[i-1] + (duration[i] - 1)
    This models the overlap day: when you fly on the departure day, you are counted in both cities.
    """
    departures = []
    # First city's departure day is its full required day count.
    departures.append(city_durations[order[0]])
    for i in range(1, len(order)):
        # Each new city adds (its required days - 1) because the flight day is shared.
        departures.append(departures[-1] + (city_durations[order[i]] - 1))
    return departures

def interval_for_city(departures, index):
    """
    Returns the day interval (start, end) of the visit for the city at given index
    in the itinerary.
    The first city is visited from day 1 to departures[0].
    For any other city (index > 0), the interval is from departures[index-1] to departures[index].
    """
    if index == 0:
        return (1, departures[0])
    else:
        return (departures[index-1], departures[index])

def satisfies_event(interval, event_window):
    """
    Check if the city's interval covers the event window.
    That is, the interval's start is <= event_window start and interval's end is >= event_window end.
    """
    start, end = interval
    win_start, win_end = event_window
    return start <= win_start and end >= win_end

# Search all permutations of the cities for a valid itinerary.
valid_order = None
valid_departures = None

for order in itertools.permutations(cities):
    # Check connectivity: every consecutive pair must have a direct flight.
    valid_connectivity = True
    for i in range(len(order) - 1):
        if order[i+1] not in flight_graph[order[i]]:
            valid_connectivity = False
            break
    if not valid_connectivity:
        continue

    # Compute departure days based on the city's required durations.
    departures = compute_departure_days(order)
    # The total trip must exactly match total_days.
    if departures[-1] != total_days:
        continue

    # Check the event constraints for the cities that have events.
    events_satisfied = True
    for event_city, event_info in events.items():
        # The event city must appear in the itinerary.
        if event_city not in order:
            events_satisfied = False
            break
        idx = order.index(event_city)
        # Get the visit interval for the event city.
        interval = interval_for_city(departures, idx)
        # Check if the interval covers the event window.
        if not satisfies_event(interval, event_info["window"]):
            events_satisfied = False
            break

    if events_satisfied:
        valid_order = order
        valid_departures = departures
        break

# If a valid itinerary is found, build the itinerary schedule.
if valid_order is None or valid_departures is None:
    result = {"itinerary": []}
else:
    itinerary = []
    for i, city in enumerate(valid_order):
        start, end = interval_for_city(valid_departures, i)
        day_range = f"Day {start}-{end}"
        itinerary.append({"day_range": day_range, "place": city})
    result = {"itinerary": itinerary}

# Output the result as JSON
print(json.dumps(result))