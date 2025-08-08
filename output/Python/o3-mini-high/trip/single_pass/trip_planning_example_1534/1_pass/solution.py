#!/usr/bin/env python3
import json
import itertools

# Define the cities and their required durations.
durations = {
    "Paris": 2,
    "Barcelona": 5,
    "Florence": 5,
    "Amsterdam": 2,
    "Tallinn": 2,
    "Vilnius": 3,
    "Warsaw": 4,
    "Venice": 3,
    "Hamburg": 4,
    "Salzburg": 4
}

# Define direct flight connections as undirected edges.
edges = [
    ("Paris", "Venice"),
    ("Barcelona", "Amsterdam"),
    ("Amsterdam", "Warsaw"),
    ("Amsterdam", "Vilnius"),
    ("Barcelona", "Warsaw"),
    ("Warsaw", "Venice"),
    ("Amsterdam", "Hamburg"),
    ("Barcelona", "Hamburg"),
    ("Barcelona", "Florence"),
    ("Barcelona", "Venice"),
    ("Paris", "Hamburg"),
    ("Paris", "Vilnius"),
    ("Paris", "Amsterdam"),
    ("Paris", "Florence"),
    ("Florence", "Amsterdam"),
    ("Vilnius", "Warsaw"),
    ("Barcelona", "Tallinn"),
    ("Paris", "Warsaw"),
    ("Tallinn", "Warsaw"),
    ("Tallinn", "Vilnius"),  # from Tallinn to Vilnius (assumed bidirectional)
    ("Amsterdam", "Tallinn"),
    ("Paris", "Tallinn"),
    ("Paris", "Barcelona"),
    ("Venice", "Hamburg"),
    ("Warsaw", "Hamburg"),
    ("Hamburg", "Salzburg"),
    ("Amsterdam", "Venice")
]

# Build the flight graph as an adjacency list (undirected).
flight_graph = {}
def add_edge(a, b):
    flight_graph.setdefault(a, set()).add(b)
    flight_graph.setdefault(b, set()).add(a)

for a, b in edges:
    add_edge(a, b)

# A helper function to compute the itinerary timeline.
# With flight overlap: first city uses full duration; every subsequent city
# starts on the same day the previous city ends.
def compute_timeline(ordering):
    timeline = []
    # For the first city, start at Day 1.
    start_day = 1
    end_day = start_day + durations[ordering[0]] - 1
    timeline.append((ordering[0], start_day, end_day))
    # For each subsequent city, flight day overlap means the city starts on previous end_day.
    for city in ordering[1:]:
        start_day = end_day  # flight day: same as previous city's end day counts for both.
        end_day = start_day + durations[city] - 1
        timeline.append((city, start_day, end_day))
    return timeline

# Check if a given time block [start, end] overlaps a required interval [req_start, req_end]
def overlaps(start, end, req_start, req_end):
    return not (end < req_start or start > req_end)

# Check that essential time-window constraints are met.
def check_time_constraints(timeline):
    for city, start, end in timeline:
        if city == "Paris":
            # Workshop in Paris between Day 1 and Day 2; Paris block must include 1 or 2.
            if not overlaps(start, end, 1, 2):
                return False
        elif city == "Barcelona":
            # Meet friends in Barcelona between Day 2 and Day 6.
            if not overlaps(start, end, 2, 6):
                return False
        elif city == "Tallinn":
            # Meet a friend in Tallinn between Day 11 and Day 12.
            if not overlaps(start, end, 11, 12):
                return False
        elif city == "Hamburg":
            # Attend a conference in Hamburg during Days 19 to 22.
            # With a 4-day stay, Hamburg should exactly cover Days 19-22.
            if start != 19 or end != 22:
                return False
        elif city == "Salzburg":
            # Wedding in Salzburg between Day 22 and Day 25.
            if start != 22 or end != 25:
                return False
    # Also total trip must finish on Day 25.
    if timeline[-1][2] != 25:
        return False
    return True

# Check connectivity: each consecutive pair in ordering must have a direct flight.
def check_connectivity(ordering):
    for i in range(len(ordering)-1):
        curr_city = ordering[i]
        next_city = ordering[i+1]
        if next_city not in flight_graph.get(curr_city, set()):
            return False
    return True

# We want to visit 10 cities in total.
# Given the event constraints, we require:
#   - The trip must start in Paris.
#   - Salzburg must be the last city (so that the wedding falls on Days 22-25).
#   - Hamburg must immediately precede Salzburg (to have the conference from Days 19-22).
# Therefore, we fix positions:
# ordering[0] = "Paris", ordering[8] = "Hamburg", ordering[9] = "Salzburg".
fixed_ordering = {0: "Paris", 8: "Hamburg", 9: "Salzburg"}
# The remaining cities to schedule (positions 1 through 7) are:
remaining_cities = {"Barcelona", "Florence", "Amsterdam", "Tallinn", "Vilnius", "Warsaw", "Venice"}

valid_itinerary = None

# Permute the 7 remaining cities over positions 1..7.
for perm in itertools.permutations(remaining_cities, 7):
    # Build a candidate ordering list of 10 cities.
    candidate = [None]*10
    candidate[0] = fixed_ordering[0]  # "Paris"
    candidate[8] = fixed_ordering[8]  # "Hamburg"
    candidate[9] = fixed_ordering[9]  # "Salzburg"
    # Fill positions 1 to 7 with the permutation.
    candidate[1:8] = list(perm)
    
    # Check flight connectivity along the order.
    if not check_connectivity(candidate):
        continue

    # Compute the timeline (each city: (city, start_day, end_day)).
    timeline = compute_timeline(candidate)
    
    # Check time-window/event constraints.
    if not check_time_constraints(timeline):
        continue

    # If all constraints are met, we have a valid itinerary.
    valid_itinerary = timeline
    break

# If a valid itinerary is found, format the output.
if valid_itinerary is None:
    output = {"itinerary": []}
else:
    itinerary_list = []
    for city, start, end in valid_itinerary:
        day_range = f"Day {start}-{end}"
        itinerary_list.append({"day_range": day_range, "place": city})
    output = {"itinerary": itinerary_list}

print(json.dumps(output))