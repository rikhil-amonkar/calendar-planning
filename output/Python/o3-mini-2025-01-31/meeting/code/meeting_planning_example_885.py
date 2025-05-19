#!/usr/bin/env python3
import itertools
import json
import sys

# Convert a time in minutes (since midnight) to H:MM (24‐hour) string.
def minutes_to_timestr(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Data for each friend: name, location, available start, available end (in minutes since midnight), meeting duration (in minutes)
# Times: 9:00 = 540, 10:00 = 600, 10:15 = 615, 9:30 = 570, 11:45 = 705, etc.
friends = [
    {
        "person": "Mark",
        "location": "Marina District",
        "avail_start": 18 * 60 + 45,   # 18:45 -> 1125
        "avail_end": 21 * 60,          # 21:00 -> 1260
        "duration": 90
    },
    {
        "person": "Karen",
        "location": "Financial District",
        "avail_start": 9 * 60 + 30,    # 9:30 -> 570
        "avail_end": 12 * 60 + 45,     # 12:45 -> 765
        "duration": 90
    },
    {
        "person": "Barbara",
        "location": "Alamo Square",
        "avail_start": 10 * 60,        # 10:00 -> 600
        "avail_end": 19 * 60 + 30,     # 19:30 -> 1170
        "duration": 90
    },
    {
        "person": "Nancy",
        "location": "Golden Gate Park",
        "avail_start": 16 * 60 + 45,   # 16:45 -> 1005
        "avail_end": 20 * 60,          # 20:00 -> 1200
        "duration": 105
    },
    {
        "person": "David",
        "location": "The Castro",
        "avail_start": 9 * 60,         # 9:00 -> 540
        "avail_end": 18 * 60,          # 18:00 -> 1080
        "duration": 120
    },
    {
        "person": "Linda",
        "location": "Bayview",
        "avail_start": 18 * 60 + 15,   # 18:15 -> 1095
        "avail_end": 19 * 60 + 45,     # 19:45 -> 1185
        "duration": 45
    },
    {
        "person": "Kevin",
        "location": "Sunset District",
        "avail_start": 10 * 60,        # 10:00 -> 600
        "avail_end": 17 * 60 + 45,     # 17:45 -> 1065
        "duration": 120
    },
    {
        "person": "Matthew",
        "location": "Haight-Ashbury",
        "avail_start": 10 * 60 + 15,   # 10:15 -> 615
        "avail_end": 15 * 60 + 30,     # 15:30 -> 930
        "duration": 45
    },
    {
        "person": "Andrew",
        "location": "Nob Hill",
        "avail_start": 11 * 60 + 45,   # 11:45 -> 705
        "avail_end": 16 * 60 + 45,     # 16:45 -> 1005
        "duration": 105
    },
]

# Travel times in minutes between locations.
# The keys are location names.
# Note: not all values are symmetric based on given dataset.
travel_times = {
    "Russian Hill": {
        "Marina District": 7,
        "Financial District": 11,
        "Alamo Square": 15,
        "Golden Gate Park": 21,
        "The Castro": 21,
        "Bayview": 23,
        "Sunset District": 23,
        "Haight-Ashbury": 17,
        "Nob Hill": 5
    },
    "Marina District": {
        "Russian Hill": 8,
        "Financial District": 17,
        "Alamo Square": 15,
        "Golden Gate Park": 18,
        "The Castro": 22,
        "Bayview": 27,
        "Sunset District": 19,
        "Haight-Ashbury": 16,
        "Nob Hill": 12
    },
    "Financial District": {
        "Russian Hill": 11,
        "Marina District": 15,
        "Alamo Square": 17,
        "Golden Gate Park": 23,
        "The Castro": 20,
        "Bayview": 19,
        "Sunset District": 30,
        "Haight-Ashbury": 19,
        "Nob Hill": 8
    },
    "Alamo Square": {
        "Russian Hill": 13,
        "Marina District": 15,
        "Financial District": 17,
        "Golden Gate Park": 9,
        "The Castro": 8,
        "Bayview": 16,
        "Sunset District": 16,
        "Haight-Ashbury": 5,
        "Nob Hill": 11
    },
    "Golden Gate Park": {
        "Russian Hill": 19,
        "Marina District": 16,
        "Financial District": 26,
        "Alamo Square": 9,
        "The Castro": 13,
        "Bayview": 23,
        "Sunset District": 10,
        "Haight-Ashbury": 7,
        "Nob Hill": 20
    },
    "The Castro": {
        "Russian Hill": 18,
        "Marina District": 21,
        "Financial District": 21,
        "Alamo Square": 8,
        "Golden Gate Park": 11,
        "Bayview": 19,
        "Sunset District": 17,
        "Haight-Ashbury": 6,
        "Nob Hill": 16
    },
    "Bayview": {
        "Russian Hill": 23,
        "Marina District": 27,
        "Financial District": 19,
        "Alamo Square": 16,
        "Golden Gate Park": 22,
        "The Castro": 19,
        "Sunset District": 23,
        "Haight-Ashbury": 19,
        "Nob Hill": 20
    },
    "Sunset District": {
        "Russian Hill": 24,
        "Marina District": 21,
        "Financial District": 30,
        "Alamo Square": 17,
        "Golden Gate Park": 11,
        "The Castro": 17,
        "Bayview": 22,
        "Haight-Ashbury": 15,
        "Nob Hill": 27
    },
    "Haight-Ashbury": {
        "Russian Hill": 17,
        "Marina District": 17,
        "Financial District": 21,
        "Alamo Square": 5,
        "Golden Gate Park": 7,
        "The Castro": 6,
        "Bayview": 18,
        "Sunset District": 15,
        "Nob Hill": 15
    },
    "Nob Hill": {
        "Russian Hill": 5,
        "Marina District": 11,
        "Financial District": 9,
        "Alamo Square": 11,
        "Golden Gate Park": 17,
        "The Castro": 17,
        "Bayview": 19,
        "Sunset District": 24,
        "Haight-Ashbury": 13
    }
}

# For completeness, add reverse directions if not provided explicitly.
def complete_travel_times(times):
    locations = list(times.keys())
    for loc in locations:
        for other in locations:
            if loc == other:
                continue
            if other not in times[loc]:
                # if missing, take from the reverse direction if available
                if loc in times[other]:
                    times[loc][other] = times[other][loc]
    return times

travel_times = complete_travel_times(travel_times)

# Starting location and time
start_location = "Russian Hill"
start_time = 9 * 60  # 9:00 -> 540 minutes

# We'll search over all permutations of the friends' list order.
# Because not every ordering may be feasible, we try to schedule as many as possible.
best_schedule = None
best_count = 0

all_friends = friends[:]  # full list of 9 friends

# Use itertools.permutations to examine orders (9! possibilities)
for perm in itertools.permutations(all_friends):
    curr_time = start_time
    curr_loc = start_location
    itinerary = []
    feasible_count = 0
    for friend in perm:
        # Calculate travel time from current location to friend's location.
        if curr_loc not in travel_times or friend["location"] not in travel_times[curr_loc]:
            travel = 9999  # large penalty if missing route
        else:
            travel = travel_times[curr_loc][friend["location"]]
        arrival_time = curr_time + travel
        # Meeting can only start when friend is available.
        meeting_start = max(arrival_time, friend["avail_start"])
        meeting_end = meeting_start + friend["duration"]
        # Check if meeting can finish before friend's available end.
        if meeting_end > friend["avail_end"]:
            # Cannot schedule this friend in this order; break out.
            break
        # Otherwise, record this meeting.
        itinerary.append({
            "action": "meet",
            "location": friend["location"],
            "person": friend["person"],
            "start_time": minutes_to_timestr(meeting_start),
            "end_time": minutes_to_timestr(meeting_end)
        })
        feasible_count += 1
        curr_time = meeting_end
        curr_loc = friend["location"]
    # If this permutation allowed more meetings than our best so far, update best_schedule.
    if feasible_count > best_count:
        best_count = feasible_count
        best_schedule = itinerary
        # If we managed to schedule all friends, we can break out of search
        if best_count == len(all_friends):
            break

# Build the result dictionary:
result = {"itinerary": best_schedule if best_schedule is not None else []}

# Output the result as JSON.
print(json.dumps(result))
    
if __name__ == '__main__':
    sys.exit(0)