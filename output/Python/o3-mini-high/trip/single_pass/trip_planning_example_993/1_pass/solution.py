#!/usr/bin/env python3
import itertools
import json

# Trip parameters
total_trip_days = 15

# Cities with required durations (in “city‐days” counting overlaps)
durations = {
    "Riga": 2,
    "Frankfurt": 3,
    "Amsterdam": 2,
    "Vilnius": 5,
    "London": 2,
    "Stockholm": 3,
    "Bucharest": 4
}

# Special time-window constraints (inclusive):
# For Amsterdam: meet friend between day 2 and day 3.
# For Vilnius: attend workshop between day 7 and day 11.
# For Stockholm: attend wedding between day 13 and day 15.
time_windows = {
    "Amsterdam": (2, 3),
    "Vilnius": (7, 11),
    "Stockholm": (13, 15)
}

# List of all cities (7 European cities)
cities = list(durations.keys())

# Flight connections.
# Most connections are bidirectional.
# We'll build a directed graph (dict of sets) where most edges are added in both directions.
flight_graph = {city: set() for city in cities}

# List of bidirectional flight pairs
bidirectional_flights = [
    ("London", "Amsterdam"),
    ("Vilnius", "Frankfurt"),
    ("Riga", "Stockholm"),
    ("London", "Bucharest"),
    ("Amsterdam", "Stockholm"),
    ("Amsterdam", "Frankfurt"),
    ("Frankfurt", "Stockholm"),
    ("Bucharest", "Riga"),
    ("Amsterdam", "Riga"),
    ("Amsterdam", "Bucharest"),
    ("Riga", "Frankfurt"),
    ("Bucharest", "Frankfurt"),
    ("London", "Frankfurt"),
    ("London", "Stockholm"),
    ("Amsterdam", "Vilnius")
]

# Add bidirectional edges
for a, b in bidirectional_flights:
    flight_graph[a].add(b)
    flight_graph[b].add(a)

# Add the one-way flight: from Riga to Vilnius (only this direction)
flight_graph["Riga"].add("Vilnius")
# Note: Vilnius to Riga is not available unless already added by a bidirectional flight (but it is not).

# Function to compute the itinerary timeline from an order.
# According to the rule: if flying on day X from city A to city B,
# then the day X counts as both the last day in A and the first day in B.
def compute_timeline(order, durations):
    timeline = []
    start_day = 1
    for city in order:
        d = durations[city]
        end_day = start_day + d - 1
        timeline.append((city, start_day, end_day))
        # Next city starts on the same day this city ends (flight day overlap)
        start_day = end_day
    return timeline

# Check if a given timeline meets the special time-window constraints.
def check_time_windows(timeline, time_windows):
    for city, (win_start, win_end) in time_windows.items():
        # Find the timeline entry for the city
        found = False
        for place, seg_start, seg_end in timeline:
            if place == city:
                # The segment must include at least one day in the window [win_start, win_end]
                if seg_start <= win_end and seg_end >= win_start:
                    found = True
                break
        if not found:
            return False
    return True

# Check if the flight transitions in the order are allowed.
def valid_flight_path(order, flight_graph):
    for i in range(len(order) - 1):
        current_city = order[i]
        next_city = order[i+1]
        if next_city not in flight_graph[current_city]:
            return False
    return True

# Since the overall days must equal total_trip_days, note that:
# Total calendar days = (sum of durations) - (number of flights)
# Here, sum(durations) is fixed = 2+3+2+5+2+3+4 = 21 and number of flights = 6,
# so 21 - 6 = 15. We will double-check timeline's last day equals total_trip_days.
def valid_timeline(timeline, total_trip_days):
    if timeline[-1][2] == total_trip_days:
        return True
    return False

# Search for a valid itinerary order.
valid_itinerary = None
for order in itertools.permutations(cities):
    # Check flight connectivity
    if not valid_flight_path(order, flight_graph):
        continue
    # Compute timeline for this order.
    timeline = compute_timeline(order, durations)
    # Check overall trip length.
    if not valid_timeline(timeline, total_trip_days):
        continue
    # Check special time-window constraints.
    if not check_time_windows(timeline, time_windows):
        continue
    # Found a valid itinerary – choose the first one.
    valid_itinerary = timeline
    break

# Create output structure.
output = {"itinerary": []}
if valid_itinerary:
    for city, start, end in valid_itinerary:
        day_range = f"Day {start}-{end}"
        output["itinerary"].append({"day_range": day_range, "place": city})
else:
    output["itinerary"].append({"error": "No valid itinerary found."})

print(json.dumps(output))