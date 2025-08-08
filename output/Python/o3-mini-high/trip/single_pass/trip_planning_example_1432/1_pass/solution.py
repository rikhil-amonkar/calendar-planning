#!/usr/bin/env python3
import json

# Total trip parameters
TOTAL_DAYS = 29
NUM_CITIES = 10

# Information about each city:
# Each city has a fixed duration.
# For some cities there is an event that forces the visit to occur with a specific start day,
# so that the city’s day‑range includes the event dates.
cities_info = {
    "Frankfurt": {"duration": 4},
    "Salzburg": {"duration": 5},
    "Athens": {"duration": 5, "event": "workshop", "required_start": 14, "event_window": [14, 18]},
    "Reykjavik": {"duration": 5},
    "Bucharest": {"duration": 3},
    "Valencia": {"duration": 2, "event": "annual show", "required_start": 5, "event_window": [5, 6]},
    "Vienna": {"duration": 5, "event": "wedding", "required_start": 6, "event_window": [6, 10]},
    "Amsterdam": {"duration": 3},
    "Stockholm": {"duration": 3, "event": "friend meeting", "event_window": [1, 3]},  # must meet friend early
    "Riga": {"duration": 3, "event": "conference", "required_start": 18, "event_window": [18, 20]}
}

# Build flight connections.
# Some flights are bidirectional; some are directional (marked with "from ... to ...")
# We'll store for each city a set of cities reachable from it.

# Initialize empty connection dictionary.
flights = {city: set() for city in cities_info}

def add_bidirectional(a, b):
    flights[a].add(b)
    flights[b].add(a)

def add_directional(a, b):
    flights[a].add(b)

# Add connections as provided:
add_bidirectional("Valencia", "Frankfurt")
add_bidirectional("Vienna", "Bucharest")
add_directional("Valencia", "Athens")         # from Valencia to Athens only
add_bidirectional("Athens", "Bucharest")
add_bidirectional("Riga", "Frankfurt")
add_bidirectional("Stockholm", "Athens")
add_bidirectional("Amsterdam", "Bucharest")
add_directional("Athens", "Riga")               # from Athens to Riga only
add_bidirectional("Amsterdam", "Frankfurt")
add_bidirectional("Stockholm", "Vienna")
add_bidirectional("Vienna", "Riga")
add_bidirectional("Amsterdam", "Reykjavik")
add_bidirectional("Reykjavik", "Frankfurt")
add_bidirectional("Stockholm", "Amsterdam")
add_bidirectional("Amsterdam", "Valencia")
add_bidirectional("Vienna", "Frankfurt")
add_bidirectional("Valencia", "Bucharest")
add_bidirectional("Bucharest", "Frankfurt")
add_bidirectional("Stockholm", "Frankfurt")
add_bidirectional("Valencia", "Vienna")
add_directional("Reykjavik", "Athens")         # from Reykjavik to Athens only
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

# Helper: Compute start day for the next city given the current itinerary.
# The rule: first city's start day is 1.
# For i > 0: start_day[i] = start_day[i-1] + (duration of previous city) - 1.
def compute_next_start(itinerary_schedule):
    if not itinerary_schedule:
        return 1
    last_city, last_start = itinerary_schedule[-1]
    d = cities_info[last_city]["duration"]
    return last_start + d - 1

# Backtracking search.
# itinerary_schedule is a list of tuples (city, start_day) in the order chosen.
# used is a set of cities already in the itinerary.
def search(itinerary_schedule, used):
    if len(itinerary_schedule) == NUM_CITIES:
        # Check that the final city's end day equals TOTAL_DAYS.
        last_city, start_day = itinerary_schedule[-1]
        d = cities_info[last_city]["duration"]
        end_day = start_day + d - 1
        if end_day == TOTAL_DAYS:
            return itinerary_schedule
        else:
            return None

    next_start = compute_next_start(itinerary_schedule)
    last_city = itinerary_schedule[-1][0]
    # Try each city not used yet.
    for city in cities_info:
        if city in used:
            continue
        # Enforce flight connectivity: must be a direct flight from last city to candidate.
        if city not in flights[last_city]:
            continue

        # For the candidate, its start day would be next_start.
        candidate_start = next_start
        # If the candidate city has a required start (from an event constraint), enforce it.
        if "required_start" in cities_info[city]:
            if candidate_start != cities_info[city]["required_start"]:
                continue
        # (For cities without a required start, we assume any start is acceptable as long as the event window can be met.
        # For Stockholm, we want to meet friend between day 1 and 3.
        # We will force Stockholm to be first.)
        # Create new itinerary entry.
        new_itinerary = itinerary_schedule + [(city, candidate_start)]
        used.add(city)
        result = search(new_itinerary, used)
        if result is not None:
            return result
        used.remove(city)
    return None

def main():
    # We require Stockholm (with friend meeting) to be the first city.
    start_schedule = [("Stockholm", 1)]
    used = {"Stockholm"}
    solution = search(start_schedule, used)
    if solution is None:
        output = {"itinerary": []}
    else:
        # Build the itinerary with day ranges.
        itinerary_list = []
        for city, start_day in solution:
            duration = cities_info[city]["duration"]
            end_day = start_day + duration - 1
            day_range = f"Day {start_day}-{end_day}"
            itinerary_list.append({"day_range": day_range, "place": city})
        output = {"itinerary": itinerary_list}
    print(json.dumps(output, indent=2))

if __name__ == "__main__":
    main()