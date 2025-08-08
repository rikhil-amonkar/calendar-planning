#!/usr/bin/env python3
import itertools
import json
import sys

# Input constraints: the cities, durations, and special event time windows.
cities = ["Santorini", "Krakow", "Paris", "Vilnius", "Munich", "Geneva", "Amsterdam", "Budapest", "Split"]

# Duration to be spent in each city.
durations = {
    "Santorini": 5,
    "Krakow": 5,
    "Paris": 5,
    "Vilnius": 3,
    "Munich": 5,
    "Geneva": 2,
    "Amsterdam": 4,
    "Budapest": 5,
    "Split": 4
}

# Special event time windows (inclusive)
# For the purpose of verifying feasibility we require that the segment for the city
# overlaps with the event window.
event_windows = {
    "Paris": (11, 15),      # meet friend in Paris between day 11 and 15
    "Krakow": (18, 22),     # wedding in Krakow between day 18 and 22
    "Santorini": (25, 29)   # meet friends in Santorini between day 25 and 29
}

# Flight network.
# For flights stated as "X and Y", add both (X,Y) and (Y,X).
# For flights stated as "from X to Y", add only (X,Y).
flights = set()

def add_bidirectional(a, b):
    flights.add((a, b))
    flights.add((b, a))

# Add undirected flights:
add_bidirectional("Paris", "Krakow")
add_bidirectional("Paris", "Amsterdam")
add_bidirectional("Paris", "Split")
# directed: from Vilnius to Munich only.
flights.add(("Vilnius", "Munich"))
add_bidirectional("Paris", "Geneva")
add_bidirectional("Amsterdam", "Geneva")
add_bidirectional("Munich", "Split")
add_bidirectional("Split", "Krakow")
add_bidirectional("Munich", "Amsterdam")
add_bidirectional("Budapest", "Amsterdam")
add_bidirectional("Split", "Geneva")
add_bidirectional("Vilnius", "Split")
add_bidirectional("Munich", "Geneva")
add_bidirectional("Munich", "Krakow")
# directed: from Krakow to Vilnius only.
flights.add(("Krakow", "Vilnius"))
add_bidirectional("Vilnius", "Amsterdam")
add_bidirectional("Budapest", "Paris")
add_bidirectional("Krakow", "Amsterdam")
add_bidirectional("Vilnius", "Paris")
add_bidirectional("Budapest", "Geneva")
add_bidirectional("Split", "Amsterdam")
add_bidirectional("Santorini", "Geneva")
add_bidirectional("Amsterdam", "Santorini")
add_bidirectional("Munich", "Budapest")
add_bidirectional("Munich", "Paris")

# Function to compute the itinerary schedule day ranges.
# According to the rule, if you fly from A to B on day X, then that day is counted for both.
# Thus, for the first city, the full duration is counted,
# and for each subsequent city, the effective additional days is (duration - 1).
def compute_schedule(order):
    schedule = []  # List of tuples: (city, start_day, end_day)
    start_day = 1
    for city in order:
        d = durations[city]
        end_day = start_day + d - 1
        schedule.append((city, start_day, end_day))
        # Next city starts on the same day the previous city ended (flight day overlap)
        start_day = end_day
    return schedule

# Check if the day segment for a given city overlaps with the event window.
def check_event(city, start_day, end_day):
    if city not in event_windows:
        return True
    window_start, window_end = event_windows[city]
    # Overlap exists if the segment's days [start_day, end_day] intersect with [window_start, window_end]
    return not (end_day < window_start or start_day > window_end)

# Check if there is a direct flight from city 'a' to city 'b'
def can_fly(a, b):
    return (a, b) in flights

# Main search: try all permutations that satisfy the flight connections and event constraints.
def find_valid_itinerary():
    # We know the events imply an order: the Paris segment must occur (in calendar days)
    # such that it overlaps with [11,15], Krakow with [18,22], and Santorini with [25,29].
    # Given the overlaps, it is natural that the travel order should have Paris first,
    # then Krakow, then Santorini.
    for perm in itertools.permutations(cities):
        # Enforce order: Paris must come before Krakow and Krakow before Santorini.
        if not (perm.index("Paris") < perm.index("Krakow") < perm.index("Santorini")):
            continue

        # Check that every consecutive pair in 'perm' has a direct flight (considering direction).
        valid_route = True
        for i in range(len(perm) - 1):
            if not can_fly(perm[i], perm[i+1]):
                valid_route = False
                break
        if not valid_route:
            continue

        # Compute the schedule day ranges.
        schedule = compute_schedule(perm)
        # The overall itinerary should sum to 30 days.
        # (Total days = sum(durations) - (number of transitions) = 38 - 8 = 30)
        if schedule[-1][2] != 30:
            # This check will always pass by the arithmetic, but include to be safe.
            continue

        # Check each event city for its required event window.
        meets_events = True
        for (city, s_day, e_day) in schedule:
            if city in event_windows:
                if not check_event(city, s_day, e_day):
                    meets_events = False
                    break
        if not meets_events:
            continue

        # Found a valid itinerary.
        return schedule

    return None

def main():
    schedule = find_valid_itinerary()
    if schedule is None:
        result = {"itinerary": []}
    else:
        # Format the schedule as required.
        itinerary_list = []
        for (city, start_day, end_day) in schedule:
            itinerary_list.append({
                "day_range": f"Day {start_day}-{end_day}",
                "place": city
            })
        result = {"itinerary": itinerary_list}
    print(json.dumps(result))

if __name__ == '__main__':
    main()