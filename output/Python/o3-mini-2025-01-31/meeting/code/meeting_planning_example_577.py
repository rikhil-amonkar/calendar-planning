#!/usr/bin/env python3
import itertools
import json

# Utility: convert time in minutes since midnight to "H:MM" string in 24-hour format (no leading zero for hour)
def minutes_to_time_str(minutes):
    hour = minutes // 60
    minute = minutes % 60
    return f"{hour}:{minute:02d}"

# Define travel times (in minutes) as a dictionary of dictionaries.
# Note: travel times are symmetric as given.
travel_times = {
    "Haight-Ashbury": {
        "Russian Hill": 17,
        "Fisherman's Wharf": 23,
        "Nob Hill": 15,
        "Golden Gate Park": 7,
        "Alamo Square": 5,
        "Pacific Heights": 12
    },
    "Russian Hill": {
        "Haight-Ashbury": 17,
        "Fisherman's Wharf": 7,
        "Nob Hill": 5,
        "Golden Gate Park": 21,
        "Alamo Square": 15,
        "Pacific Heights": 7
    },
    "Fisherman's Wharf": {
        "Haight-Ashbury": 22,
        "Russian Hill": 7,
        "Nob Hill": 11,
        "Golden Gate Park": 25,
        "Alamo Square": 20,
        "Pacific Heights": 12
    },
    "Nob Hill": {
        "Haight-Ashbury": 13,
        "Russian Hill": 5,
        "Fisherman's Wharf": 11,
        "Golden Gate Park": 17,
        "Alamo Square": 11,
        "Pacific Heights": 8
    },
    "Golden Gate Park": {
        "Haight-Ashbury": 7,
        "Russian Hill": 19,
        "Fisherman's Wharf": 24,
        "Nob Hill": 20,
        "Alamo Square": 10,
        "Pacific Heights": 16
    },
    "Alamo Square": {
        "Haight-Ashbury": 5,
        "Russian Hill": 13,
        "Fisherman's Wharf": 19,
        "Nob Hill": 11,
        "Golden Gate Park": 9,
        "Pacific Heights": 10
    },
    "Pacific Heights": {
        "Haight-Ashbury": 11,
        "Russian Hill": 7,
        "Fisherman's Wharf": 13,
        "Nob Hill": 8,
        "Golden Gate Park": 15,
        "Alamo Square": 10
    }
}

# Define the meeting constraints.
# Times will be represented as minutes since midnight.
# Convert HH:MM to minutes after midnight.
def time_to_minutes(time_str):
    parts = time_str.split(":")
    return int(parts[0]) * 60 + int(parts[1])

# Starting location and time.
start_location = "Haight-Ashbury"
start_time = time_to_minutes("9:00")  # 9:00 AM -> 540 minutes

# List of meetings (person, location, available start, available end, minimum duration)
meetings = [
    {
        "person": "Stephanie",
        "location": "Russian Hill",
        "avail_start": time_to_minutes("20:00"),
        "avail_end": time_to_minutes("20:45"),
        "duration": 15
    },
    {
        "person": "Kevin",
        "location": "Fisherman's Wharf",
        "avail_start": time_to_minutes("19:15"),
        "avail_end": time_to_minutes("21:45"),
        "duration": 75
    },
    {
        "person": "Robert",
        "location": "Nob Hill",
        "avail_start": time_to_minutes("7:45"),
        "avail_end": time_to_minutes("10:30"),
        "duration": 90
    },
    {
        "person": "Steven",
        "location": "Golden Gate Park",
        "avail_start": time_to_minutes("8:30"),
        "avail_end": time_to_minutes("17:00"),
        "duration": 75
    },
    {
        "person": "Anthony",
        "location": "Alamo Square",
        "avail_start": time_to_minutes("7:45"),
        "avail_end": time_to_minutes("19:45"),
        "duration": 15
    },
    {
        "person": "Sandra",
        "location": "Pacific Heights",
        "avail_start": time_to_minutes("14:45"),
        "avail_end": time_to_minutes("21:45"),
        "duration": 45
    }
]

# Our goal is to meet as many friends as possible.
# We'll try different orders of meetings (permutations) and schedule them if possible.
# Each schedule simulation:
#   current_time: when we are ready to leave current location.
#   current_location: our current location.
#   For each meeting, determine travel time, earliest arrival, wait for meeting's avail_start if needed.
#   Then meeting start = max(arrival_time, meeting availability start)
#   Meeting end = meeting start + required duration. Must not exceed meeting availability end.
#   If meeting cannot be scheduled, then this order is not feasible (or we record the sub-schedule count).
# We want the schedule with the maximum number of meetings (and must use computed times).

def simulate_schedule(order):
    itinerary = []
    current_time = start_time
    current_location = start_location
    count = 0

    for meet in order:
        # Check travel time from current_location to meeting location
        if current_location == meet["location"]:
            travel = 0
        else:
            travel = travel_times[current_location][meet["location"]]
        arrival_time = current_time + travel
        # Wait if arrived before available start
        meeting_start = max(arrival_time, meet["avail_start"])
        meeting_end = meeting_start + meet["duration"]
        # Check if meeting finishes within availability
        if meeting_end > meet["avail_end"]:
            # Not feasible to schedule this meeting in order
            return itinerary, count
        # Add meeting to itinerary
        itinerary.append({
            "action": "meet",
            "location": meet["location"],
            "person": meet["person"],
            "start_time": minutes_to_time_str(meeting_start),
            "end_time": minutes_to_time_str(meeting_end)
        })
        # Update current time and location
        current_time = meeting_end
        current_location = meet["location"]
        count += 1
    return itinerary, count

# We'll search over all permutations to maximize the number of meetings scheduled.
# Since the goal is to meet as many friends as possible, we use full order if possible;
# but if not, we can use a partial schedule.
all_meetings = meetings[:]  # all six
best_itinerary = []
max_count = 0

# We generate all permutations of the meetings list.
for perm in itertools.permutations(all_meetings):
    itinerary, count = simulate_schedule(perm)
    # update best if count is higher
    if count > max_count:
        max_count = count
        best_itinerary = itinerary
    # Early exit if we scheduled all meetings
    if max_count == len(all_meetings):
        break

# In our problem, Robert's meeting is hard to schedule given our starting time,
# so the optimal number usually is less than six.
# Now output the result in JSON format as specified.
result = {
    "itinerary": best_itinerary
}

print(json.dumps(result, indent=2))