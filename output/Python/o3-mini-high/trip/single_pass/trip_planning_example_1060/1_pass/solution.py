#!/usr/bin/env python3
import json
import itertools

# Total trip days
total_days = 25

# Cities with their required durations (in days)
city_durations = {
    "Reykjavik": 4,  # workshop between day1-4 must happen here
    "Stuttgart": 4,  # conference on day4 and day7 must happen here
    "Valencia": 5,
    "Seville": 3,
    "Munich": 3,    # annual show must be between day13-15
    "Geneva": 5,
    "Istanbul": 4,  # visit relatives between day19-22
    "Vilnius": 4
}

# Event constraints: For cities with fixed event date requirements, 
# the flight arrival day must equal the event start.
# For a city with duration d, the segment covers: start_day, start_day+1, ..., start_day+d-1
# We require:
# Reykjavik: workshop must occur between day1 and day4; we force it as the first city with start = 1.
# Stuttgart: conference on days 4 and 7; so if it is the second city then it must start on day4.
# Munich (duration 3): to cover days 13,14,15, its start day must be 13.
# Istanbul (duration 4): to cover days 19,20,21,22, its start day must be 19.
event_start_constraints = {
    "Reykjavik": 1,
    "Stuttgart": 4,
    "Munich": 13,
    "Istanbul": 19
}

# Define the available direct flight connections.
# For flights listed as "X and Y" we assume bidirectional.
# For ones listed as "from X to Y", only the indicated direction is allowed.
cities = list(city_durations.keys())
# Initialize flight graph for each city as an empty set.
flight_graph = {city: set() for city in cities}

# Add bidirectional edges:
def add_bidirectional(a, b):
    flight_graph[a].add(b)
    flight_graph[b].add(a)

# 1. Geneva and Istanbul
add_bidirectional("Geneva", "Istanbul")
# 2. Reykjavik and Munich
add_bidirectional("Reykjavik", "Munich")
# 3. Stuttgart and Valencia
add_bidirectional("Stuttgart", "Valencia")
# 4. from Reykjavik to Stuttgart (directional)
flight_graph["Reykjavik"].add("Stuttgart")
# 5. Stuttgart and Istanbul
add_bidirectional("Stuttgart", "Istanbul")
# 6. Munich and Geneva
add_bidirectional("Munich", "Geneva")
# 7. Istanbul and Vilnius
add_bidirectional("Istanbul", "Vilnius")
# 8. Valencia and Seville
add_bidirectional("Valencia", "Seville")
# 9. Valencia and Istanbul
add_bidirectional("Valencia", "Istanbul")
# 10. from Vilnius to Munich (directional)
flight_graph["Vilnius"].add("Munich")
# 11. Seville and Munich
add_bidirectional("Seville", "Munich")
# 12. Munich and Istanbul
add_bidirectional("Munich", "Istanbul")
# 13. Valencia and Geneva
add_bidirectional("Valencia", "Geneva")
# 14. Valencia and Munich
add_bidirectional("Valencia", "Munich")

# Fixed starting segments based on event time constraints:
# S1 must be Reykjavik (for the workshop) and S2 must be Stuttgart (for the conference).
fixed_order = ["Reykjavik", "Stuttgart"]

# The remaining cities to schedule (order to be determined)
remaining_cities = [c for c in city_durations if c not in fixed_order]

# Function to compute the schedule given an order.
# The itinerary schedule is computed as follows:
# For the first segment, start_day is fixed at 1.
# For each subsequent segment, its start_day equals the previous segment's end_day (flight day overlap).
# And end_day = start_day + duration - 1.
def compute_schedule(order):
    schedule = []
    current_day = 1
    for city in order:
        d = city_durations[city]
        start_day = current_day
        end_day = start_day + d - 1
        schedule.append((city, start_day, end_day))
        # For the next city the start day is the same as the end day (flight overlap)
        current_day = end_day
    return schedule

# Check if an itinerary (order and schedule) satisfies:
#   1. Flight connectivity (each consecutive pair has a direct flight in the proper direction).
#   2. The final end day equals the total trip days.
#   3. Event start constraints for cities with events.
def itinerary_is_valid(full_order, schedule):
    # Check flight connectivity between each consecutive pair
    for i in range(len(full_order) - 1):
        current_city = full_order[i]
        next_city = full_order[i+1]
        if next_city not in flight_graph[current_city]:
            return False
    # Check that the overall trip ends on the designated total_days.
    if schedule[-1][2] != total_days:
        return False
    # Check event constraints
    for city, start, end in schedule:
        if city in event_start_constraints:
            if start != event_start_constraints[city]:
                return False
    return True

# Search for a valid permutation of the remaining cities among segments S3...S8.
valid_schedule = None
valid_order = None

for perm in itertools.permutations(remaining_cities):
    full_order = fixed_order + list(perm)
    sched = compute_schedule(full_order)
    if itinerary_is_valid(full_order, sched):
        valid_schedule = sched
        valid_order = full_order
        break

if not valid_schedule:
    # If no valid itinerary is found, output an error JSON.
    result = {"itinerary": "No valid itinerary found with the given constraints."}
    print(json.dumps(result))
    exit(0)

# Build the JSON output structure.
# Each segment will be represented with its day range and the corresponding city.
itinerary_output = []
for city, start, end in valid_schedule:
    day_range = f"Day {start}-{end}"
    itinerary_output.append({"day_range": day_range, "place": city})

output = {"itinerary": itinerary_output}

# Output the result in JSON format.
print(json.dumps(output, indent=2))