import itertools
import json

# Input variables
total_days = 23
cities = ["Amsterdam", "Edinburgh", "Brussels", "Vienna", "Berlin", "Reykjavik"]
durations = {
    "Amsterdam": 4,
    "Edinburgh": 5,
    "Brussels": 5,
    "Vienna": 5,
    "Berlin": 4,
    "Reykjavik": 5
}

# Direct flight connections (treated as bidirectional)
flight_connections = {
    frozenset(("Edinburgh", "Berlin")),
    frozenset(("Amsterdam", "Berlin")),
    frozenset(("Edinburgh", "Amsterdam")),
    frozenset(("Vienna", "Berlin")),
    frozenset(("Berlin", "Brussels")),
    frozenset(("Vienna", "Reykjavik")),
    frozenset(("Edinburgh", "Brussels")),
    frozenset(("Vienna", "Brussels")),
    frozenset(("Amsterdam", "Reykjavik")),
    frozenset(("Reykjavik", "Brussels")),
    frozenset(("Amsterdam", "Vienna")),
    frozenset(("Reykjavik", "Berlin"))
}

# Event constraints:
# The tuple (L, U) means that if the city is visited in an interval [S, E],
# then we require that the interval intersect the event window [L, U].
event_constraints = {
    "Amsterdam": (5, 8),    # Visit relatives between day 5 and 8
    "Berlin": (16, 19),     # Meet a friend in Berlin between day 16 and 19
    "Reykjavik": (12, 16)   # Attend a workshop in Reykjavik between day 12 and 16
}

def compute_schedule(itinerary):
    """
    Given an itinerary (a tuple/list of cities in order),
    compute a schedule where if you fly on day X,
    then you are in both cities on that day.
    The first city is from day 1 to (duration),
    and for each subsequent city, the start day equals
    the previous city's end day.
    Returns a list of dictionaries with keys: city, start, end.
    """
    schedule = []
    current_day = 1
    for city in itinerary:
        # In each city, you spend its full duration.
        # On the day of transition, you are assumed to be in both cities.
        end_day = current_day + durations[city] - 1
        schedule.append({"city": city, "start": current_day, "end": end_day})
        # Next city starts on the same day you ended the previous city (overlap day)
        current_day = end_day
    return schedule

def meets_event_constraints(schedule):
    """
    For every city that has an event constraint, check that
    its scheduled interval [start, end] intersects the event window.
    (i.e. schedule_end >= event_start and schedule_start <= event_end)
    """
    for segment in schedule:
        city = segment["city"]
        start = segment["start"]
        end = segment["end"]
        if city in event_constraints:
            event_start, event_end = event_constraints[city]
            # The scheduled interval must overlap the event window.
            if end < event_start or start > event_end:
                return False
    return True

def valid_flight_sequence(itinerary):
    """
    Check that every consecutive pair in the itinerary
    is connected by a direct flight.
    """
    for i in range(len(itinerary) - 1):
        if frozenset((itinerary[i], itinerary[i+1])) not in flight_connections:
            return False
    return True

def find_itinerary():
    # Try every permutation of cities until one meets the constraints
    for perm in itertools.permutations(cities):
        if not valid_flight_sequence(perm):
            continue
        sched = compute_schedule(perm)
        # Check that the overall trip uses the expected total days.
        if sched[-1]["end"] != total_days:
            continue
        if meets_event_constraints(sched):
            return sched
    return None

schedule = find_itinerary()

if schedule is None:
    result = {"itinerary": []}
else:
    # Format the schedule into the required JSON structure.
    itinerary_output = []
    for segment in schedule:
        day_range = f"Day {segment['start']}-{segment['end']}"
        itinerary_output.append({"day_range": day_range, "place": segment["city"]})
    result = {"itinerary": itinerary_output}

print(json.dumps(result))