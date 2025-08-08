#!/usr/bin/env python3
import json
import itertools

# Helper functions to convert between minutes (since midnight) and time strings.
def minutes_to_time_str(minutes):
    hour = minutes // 60
    minute = minutes % 60
    return f"{hour}:{minute:02d}"

# Define meeting constraints.
# Times are represented in minutes since midnight.
# Sunset District: arrival at 9:00 -> 540 minutes.
meetings = [
    {
        "person": "Daniel",
        "location": "Golden Gate Park",
        "avail_start": 8 * 60,         # 8:00 -> 480
        "avail_end": 13 * 60 + 30,     # 13:30 -> 810
        "duration": 15
    },
    {
        "person": "Margaret",
        "location": "Russian Hill",
        "avail_start": 9 * 60,         # 9:00 -> 540
        "avail_end": 16 * 60,          # 16:00 -> 960
        "duration": 30
    },
    {
        "person": "Charles",
        "location": "Alamo Square",
        "avail_start": 18 * 60,        # 18:00 -> 1080
        "avail_end": 20 * 60 + 45,     # 20:45 -> 1245
        "duration": 90
    },
    {
        "person": "Stephanie",
        "location": "Mission District",
        "avail_start": 20 * 60 + 30,   # 20:30 -> 1230
        "avail_end": 22 * 60,          # 22:00 -> 1320
        "duration": 90
    }
]

# Define travel times in minutes between locations.
# The keys are tuples: (from_location, to_location)
travel_times = {
    ("Sunset District", "Alamo Square"): 17,
    ("Sunset District", "Russian Hill"): 24,
    ("Sunset District", "Golden Gate Park"): 11,
    ("Sunset District", "Mission District"): 24,
    
    ("Alamo Square", "Sunset District"): 16,
    ("Alamo Square", "Russian Hill"): 13,
    ("Alamo Square", "Golden Gate Park"): 9,
    ("Alamo Square", "Mission District"): 10,
    
    ("Russian Hill", "Sunset District"): 23,
    ("Russian Hill", "Alamo Square"): 15,
    ("Russian Hill", "Golden Gate Park"): 21,
    ("Russian Hill", "Mission District"): 16,
    
    ("Golden Gate Park", "Sunset District"): 10,
    ("Golden Gate Park", "Alamo Square"): 10,
    ("Golden Gate Park", "Russian Hill"): 19,
    ("Golden Gate Park", "Mission District"): 17,
    
    ("Mission District", "Sunset District"): 24,
    ("Mission District", "Alamo Square"): 11,
    ("Mission District", "Russian Hill"): 15,
    ("Mission District", "Golden Gate Park"): 17,
}

# Initial conditions
initial_location = "Sunset District"
start_time = 9 * 60  # 9:00 -> 540 minutes

# Function to simulate a given ordering of meetings.
# It returns a tuple (schedule_events, final_time) if the ordering is feasible, otherwise (None, None).
def simulate_schedule(order):
    current_time = start_time
    current_location = initial_location
    events = []
    for meeting in order:
        # Get travel time from current location to next meeting's location.
        if (current_location, meeting["location"]) not in travel_times:
            return None, None  # No travel info available.
        travel_time = travel_times[(current_location, meeting["location"])]
        arrival_time = current_time + travel_time
        # Wait if arrived before the meeting's availability start.
        meeting_start = max(arrival_time, meeting["avail_start"])
        meeting_end = meeting_start + meeting["duration"]
        # Check if we can finish the meeting before the person's availability ends.
        if meeting_end > meeting["avail_end"]:
            return None, None  # Infeasible schedule.
        events.append({
            "action": "meet",
            "location": meeting["location"],
            "person": meeting["person"],
            "start_time": minutes_to_time_str(meeting_start),
            "end_time": minutes_to_time_str(meeting_end)
        })
        # Update current location and time.
        current_time = meeting_end
        current_location = meeting["location"]
    return events, current_time

# We want to maximize number of meetings met.
# We will check all orderings (including possible subsets if not all meetings can be scheduled).
best_schedule = None
max_meetings = 0
best_finish_time = float('inf')

# First try all full permutations of all meetings.
n = len(meetings)
for perm in itertools.permutations(meetings, n):
    events, finish_time = simulate_schedule(perm)
    if events is not None:
        if n > max_meetings:
            max_meetings = n
            best_finish_time = finish_time
            best_schedule = events
        elif n == max_meetings and finish_time < best_finish_time:
            best_finish_time = finish_time
            best_schedule = events

# If no full schedule is feasible, try smaller subsets.
if best_schedule is None:
    for r in range(n-1, 0, -1):
        for subset in itertools.permutations(meetings, r):
            events, finish_time = simulate_schedule(subset)
            if events is not None:
                if r > max_meetings:
                    max_meetings = r
                    best_finish_time = finish_time
                    best_schedule = events
                elif r == max_meetings and finish_time < best_finish_time:
                    best_finish_time = finish_time
                    best_schedule = events
        if best_schedule is not None:
            break

# Prepare the JSON output.
result = {"itinerary": best_schedule if best_schedule is not None else []}
print(json.dumps(result))