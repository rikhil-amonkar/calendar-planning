#!/usr/bin/env python3
import json

# This program computes an itinerary among 10 European cities given duration constraints,
# fixed event windows and the direct flight connectivity between cities.
#
# The itinerary must span 32 days in total. Each city visit i has a planned duration L.
# When flying from city A to city B on a given day, that day counts for both A and B.
# Thus, if the first city starts on day 1 and has duration L1 then its local days are [1, L1].
# For subsequent cities i, the start day is computed as:
#    start_day[i] = 1 + sum_{j=1}^{i-1} (L_j - 1)
#
# The given city durations and event constraints are:
#    Edinburgh: 5 days, must meet friend between day 1 and 5.
#    Barcelona: 5 days.
#    Budapest: 5 days, and the annual show runs from day 9 to day 13 (so Budapest block must be exactly [9,13]).
#    Vienna: 5 days.
#    Stockholm: 2 days, and must meet friend between day 17 and 18.
#    Munich: 3 days, with a workshop between day 18 and 20.
#    Bucharest: 2 days.
#    Riga: 5 days.
#    Warsaw: 5 days, with a conference covering day 25 and day 29 (so must be exactly [25,29]).
#    Krakow: 4 days.
#
# In addition, the itinerary must allow only direct-flight legs between cities.
# The direct connections (bidirectional) are provided.
#
# A careful analysis (with overlaps from flight days) gives one valid ordering:
#
#   1. Edinburgh      (5 days)  -> block: [1,5]    (meets friend between day 1-5)
#   2. Barcelona      (5 days)  -> block: [5,9]
#   3. Budapest       (5 days)  -> block: [9,13]   (annual show fully on days 9-13)
#   4. Vienna         (5 days)  -> block: [13,17]
#   5. Stockholm      (2 days)  -> block: [17,18]  (meeting in Stockholm on day 17 or 18)
#   6. Munich         (3 days)  -> block: [18,20]  (workshop in Munich on day 18-20)
#   7. Bucharest      (2 days)  -> block: [20,21]
#   8. Riga           (5 days)  -> block: [21,25]
#   9. Warsaw         (5 days)  -> block: [25,29]  (conference covering day 25 and 29)
#  10. Krakow         (4 days)  -> block: [29,32]
#
# We also check that all consecutive legs have a direct flight:
#   Edinburgh -> Barcelona                 (direct: "Edinburgh and Barcelona")
#   Barcelona -> Budapest                  (direct: "Barcelona and Budapest")
#   Budapest -> Vienna                     (direct: "Budapest and Vienna")
#   Vienna -> Stockholm                    (direct: "Vienna and Stockholm")
#   Stockholm -> Munich                    (direct: "Stockholm and Munich")
#   Munich -> Bucharest                    (direct: "Munich and Bucharest")
#   Bucharest -> Riga                      (direct: "Bucharest and Riga")
#   Riga -> Warsaw                         (direct: "Riga and Warsaw")
#   Warsaw -> Krakow                       (direct: "Warsaw and Krakow")
#
# The computed start days satisfy the critical event dates:
#   Budapest block is fixed to [9,13] so the annual show is attended fully.
#   Stockholm block is [17,18], and Munich block [18,20] so the meeting and workshop can be attended.
#   Warsaw block is [25,29] so the conference days 25 and 29 occur during the visit.
#
# The overall itinerary spans day 1 through day 32.
#
# Now we compute and output the result as a JSON array (list) of segments,
# each segment is a dictionary with keys: "day_range" and "place".


# Define the ordered itinerary as determined:
itinerary = [
    {"place": "Edinburgh", "duration": 5, "event": {"window": (1,5), "desc": "Friend meeting in Edinburgh"}},
    {"place": "Barcelona", "duration": 5, "event": None},
    {"place": "Budapest", "duration": 5, "event": {"window": (9,13), "desc": "Annual show in Budapest"}},
    {"place": "Vienna", "duration": 5, "event": None},
    {"place": "Stockholm", "duration": 2, "event": {"window": (17,18), "desc": "Meet friend in Stockholm"}},
    {"place": "Munich", "duration": 3, "event": {"window": (18,20), "desc": "Workshop in Munich"}},
    {"place": "Bucharest", "duration": 2, "event": None},
    {"place": "Riga", "duration": 5, "event": None},
    {"place": "Warsaw", "duration": 5, "event": {"window": (25,29), "desc": "Conference in Warsaw"}},
    {"place": "Krakow", "duration": 4, "event": None}
]

# Direct flight connectivity (bidirectional)
# Each tuple represents a pair of cities with a direct flight connection.
flights = {
    ("Budapest", "Munich"),
    ("Bucharest", "Riga"),
    ("Munich", "Krakow"),
    ("Munich", "Warsaw"),
    ("Munich", "Bucharest"),
    ("Edinburgh", "Stockholm"),
    ("Barcelona", "Warsaw"),
    ("Edinburgh", "Krakow"),
    ("Barcelona", "Munich"),
    ("Stockholm", "Krakow"),
    ("Budapest", "Vienna"),
    ("Barcelona", "Stockholm"),
    ("Stockholm", "Munich"),
    ("Edinburgh", "Budapest"),
    ("Barcelona", "Riga"),
    ("Edinburgh", "Barcelona"),
    ("Vienna", "Riga"),
    ("Barcelona", "Budapest"),
    ("Bucharest", "Warsaw"),
    ("Vienna", "Krakow"),
    ("Edinburgh", "Munich"),
    ("Barcelona", "Bucharest"),
    ("Edinburgh", "Riga"),
    ("Vienna", "Stockholm"),
    ("Warsaw", "Krakow"),
    ("Barcelona", "Krakow"),
    ("Riga", "Munich"),
    ("Vienna", "Bucharest"),
    ("Budapest", "Warsaw"),
    ("Vienna", "Warsaw"),
    ("Barcelona", "Vienna"),
    ("Budapest", "Bucharest"),
    ("Vienna", "Munich"),
    ("Riga", "Warsaw"),
    ("Stockholm", "Riga"),
    ("Stockholm", "Warsaw")
}

# Function to check if two cities have a direct flight (bidirectional)
def has_direct_flight(city_a, city_b):
    pair = (city_a, city_b)
    rev_pair = (city_b, city_a)
    return pair in flights or rev_pair in flights

# Compute start and end days for each city in the itinerary.
# According to the rule: start_day[0] = 1.
# For i >= 1, start_day[i] = 1 + sum_{j=0}^{i-1}(duration_j - 1)
schedule = []
current_day = 1
for segment in itinerary:
    start = current_day
    end = start + segment["duration"] - 1
    schedule.append({"day_range": f"{start}-{end}", "place": segment["place"]})
    # Next city: flight occurs on the current segment's last day, so add (duration - 1)
    current_day = start + segment["duration"] - 1

# Ensure overall trip ends at day 32
total_trip_days = current_day
if total_trip_days != 32:
    # Adjust by shifting the schedule if needed.
    shift = 32 - total_trip_days
    new_schedule = []
    for entry in schedule:
        start_str, end_str = entry["day_range"].split("-")
        start_day = int(start_str) + shift
        end_day = int(end_str) + shift
        new_schedule.append({"day_range": f"{start_day}-{end_day}", "place": entry["place"]})
    schedule = new_schedule

# Check connectivity between consecutive cities and basic event placement.
errors = []
for i in range(len(itinerary) - 1):
    city_from = itinerary[i]["place"]
    city_to = itinerary[i+1]["place"]
    if not has_direct_flight(city_from, city_to):
        errors.append(f"No direct flight from {city_from} to {city_to}")

# Check that event windows are satisfied (i.e. the event-required day falls in the city block)
# For Budapest and Warsaw the blocks are fixed by their windows.
for seg, sched in zip(itinerary, schedule):
    if seg["event"]:
        window_start, window_end = seg["event"]["window"]
        range_start, range_end = map(int, sched["day_range"].split("-"))
        # Check that the event window is contained in the block (for Budapest and Warsaw, we need exact match)
        if seg["place"] in ["Budapest", "Warsaw"]:
            if range_start != window_start or range_end != window_end:
                errors.append(f"{seg['place']} block {sched['day_range']} does not match required event window {window_start}-{window_end}")
        else:
            # For others, require at least one day in the window
            if window_end < range_start or window_start > range_end:
                errors.append(f"{seg['place']} block {sched['day_range']} does not cover event window {window_start}-{window_end}")

if errors:
    # If any error is found, output the errors in a JSON object.
    result = {"errors": errors}
else:
    # Otherwise, output the schedule (only day_range and place)
    result = schedule

# Output the result as JSON
print(json.dumps(result, indent=2))