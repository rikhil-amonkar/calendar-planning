#!/usr/bin/env python3
import json
import itertools

# Helper function to convert minutes (since midnight) to "H:MM" 24-hour format (no leading zero for hours)
def minutes_to_time_str(minutes):
    hrs = minutes // 60
    mins = minutes % 60
    return f"{hrs}:{mins:02d}"

# Travel times in minutes between locations as given in the problem.
# The keys are tuples: (origin, destination)
travel_times = {
    ("Sunset District", "Alamo Square"): 17,
    ("Sunset District", "Russian Hill"): 24,
    ("Sunset District", "Presidio"): 16,
    ("Sunset District", "Financial District"): 30,
    ("Alamo Square", "Sunset District"): 16,
    ("Alamo Square", "Russian Hill"): 13,
    ("Alamo Square", "Presidio"): 18,
    ("Alamo Square", "Financial District"): 17,
    ("Russian Hill", "Sunset District"): 23,
    ("Russian Hill", "Alamo Square"): 15,
    ("Russian Hill", "Presidio"): 14,
    ("Russian Hill", "Financial District"): 11,
    ("Presidio", "Sunset District"): 15,
    ("Presidio", "Alamo Square"): 18,
    ("Presidio", "Russian Hill"): 14,
    ("Presidio", "Financial District"): 23,
    ("Financial District", "Sunset District"): 31,
    ("Financial District", "Alamo Square"): 17,
    ("Financial District", "Russian Hill"): 10,
    ("Financial District", "Presidio"): 22,
}

# Meeting constraint definitions.
# Times are in minutes from midnight.
# For example 9:00 AM is 540 minutes.
meetings = {
    "Kevin": {
        "location": "Alamo Square",
        "available_start": 8*60 + 15,  # 8:15 -> 495
        "available_end": 21*60 + 30,   # 21:30 -> 1290
        "duration": 75
    },
    "Kimberly": {
        "location": "Russian Hill",
        "available_start": 8*60 + 45,  # 8:45 -> 525
        "available_end": 12*60 + 30,   # 12:30 -> 750
        "duration": 30
    },
    "Joseph": {
        "location": "Presidio",
        "available_start": 18*60 + 30,  # 18:30 -> 1110
        "available_end": 19*60 + 15,    # 19:15 -> 1155
        "duration": 45
    },
    "Thomas": {
        "location": "Financial District",
        "available_start": 19*60,      # 19:00 -> 1140
        "available_end": 21*60 + 45,     # 21:45 -> 1305
        "duration": 45
    }
}

# Starting parameters
start_location = "Sunset District"
start_time = 9 * 60  # 9:00 AM -> 540 minutes

# We'll search through all permutations of the four meetings to find a feasible schedule.
# A schedule is feasible if meeting start time (taking into account travel and waiting) is within the person's availability window,
# and if the meeting can run for the minimum required duration and finish by their availability end.
def evaluate_schedule(order):
    itinerary = []
    current_loc = start_location
    current_time = start_time
    total_wait = 0
    for person in order:
        meeting = meetings[person]
        dest = meeting["location"]
        # Get travel time from current location to destination.
        travel_time = travel_times.get((current_loc, dest), None)
        if travel_time is None:
            # In case travel time not defined, skip this itinerary.
            return None
        arrival_time = current_time + travel_time
        # The meeting cannot start before the person's available start.
        meeting_start = max(arrival_time, meeting["available_start"])
        # Calculate waiting time if any.
        waiting = meeting_start - arrival_time
        total_wait += waiting
        meeting_end = meeting_start + meeting["duration"]
        # Check if meeting ends before the person's available end.
        if meeting_end > meeting["available_end"]:
            return None  # This ordering is not feasible.
        # Record the meeting details.
        itinerary.append({
            "action": "meet",
            "location": dest,
            "person": person,
            "start_time": minutes_to_time_str(meeting_start),
            "end_time": minutes_to_time_str(meeting_end)
        })
        # Set current_time and current location for next meeting.
        current_time = meeting_end
        current_loc = dest
    # Return the itinerary along with a metric (final finishing time, total waiting) for selection.
    return {
        "itinerary": itinerary,
        "final_time": current_time,
        "total_wait": total_wait
    }

# Generate all permutations of meeting orders (list of person names)
all_persons = list(meetings.keys())
feasible_schedules = []
for order in itertools.permutations(all_persons):
    result = evaluate_schedule(order)
    if result is not None:
        feasible_schedules.append((order, result))

# Choose the best schedule.
# Our optimization goal: maximize number of meetings. All feasible ones here have 4 meetings.
# Tie-breaker: earliest final finishing time, then minimal waiting time.
if feasible_schedules:
    # Sort by (final_time, total_wait)
    feasible_schedules.sort(key=lambda x: (x[1]["final_time"], x[1]["total_wait"]))
    best_schedule = feasible_schedules[0][1]
    # Remove additional timing metrics before output.
    output = {"itinerary": best_schedule["itinerary"]}
else:
    output = {"itinerary": []}

# Output the schedule as JSON.
print(json.dumps(output, indent=2))
                        
if __name__ == '__main__':
    pass