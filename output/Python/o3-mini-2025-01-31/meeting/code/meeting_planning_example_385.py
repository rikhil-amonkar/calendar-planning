#!/usr/bin/env python3
import json
from itertools import permutations

# Helper functions to convert time formats
def time_to_minutes(time_str):
    # Expects "H:MM" where H may have no leading zero.
    parts = time_str.split(':')
    return int(parts[0]) * 60 + int(parts[1])

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Travel times in minutes (using consistent location names)
travel_times = {
    ("Nob Hill", "Presidio"): 17,
    ("Nob Hill", "North Beach"): 8,
    ("Nob Hill", "Fisherman's Wharf"): 11,
    ("Nob Hill", "Pacific Heights"): 8,
    ("Presidio", "Nob Hill"): 18,
    ("Presidio", "North Beach"): 18,
    ("Presidio", "Fisherman's Wharf"): 19,
    ("Presidio", "Pacific Heights"): 11,
    ("North Beach", "Nob Hill"): 7,
    ("North Beach", "Presidio"): 17,
    ("North Beach", "Fisherman's Wharf"): 5,
    ("North Beach", "Pacific Heights"): 8,
    ("Fisherman's Wharf", "Nob Hill"): 11,
    ("Fisherman's Wharf", "Presidio"): 17,
    ("Fisherman's Wharf", "North Beach"): 6,
    ("Fisherman's Wharf", "Pacific Heights"): 12,
    ("Pacific Heights", "Nob Hill"): 8,
    ("Pacific Heights", "Presidio"): 11,
    ("Pacific Heights", "North Beach"): 9,
    ("Pacific Heights", "Fisherman's Wharf"): 13,
}

# Meeting constraints and parameters.
# Times are stored as minutes since midnight.
meetings = [
    {
        "person": "Jeffrey",
        "location": "Presidio",
        "avail_start": time_to_minutes("8:00"),
        "avail_end": time_to_minutes("10:00"),
        "min_duration": 105
    },
    {
        "person": "Steven",
        "location": "North Beach",
        "avail_start": time_to_minutes("13:30"),
        "avail_end": time_to_minutes("22:00"),
        "min_duration": 45
    },
    {
        "person": "Barbara",
        "location": "Fisherman's Wharf",
        "avail_start": time_to_minutes("18:00"),
        "avail_end": time_to_minutes("21:30"),
        "min_duration": 30
    },
    {
        "person": "John",
        "location": "Pacific Heights",
        "avail_start": time_to_minutes("9:00"),
        "avail_end": time_to_minutes("13:30"),
        "min_duration": 15
    }
]

# Starting parameters
start_location = "Nob Hill"
start_time = time_to_minutes("9:00")

def get_travel_time(frm, to):
    return travel_times.get((frm, to), float('inf'))

# Evaluate a given order of meetings;
# Returns (feasible, schedule, final_time)
def evaluate_schedule(order):
    current_time = start_time
    current_location = start_location
    schedule = []
    
    for meeting in order:
        # Travel from current location to meeting location
        travel_time = get_travel_time(current_location, meeting["location"])
        arrival_time = current_time + travel_time
        
        # Meeting can only start after meeting's avail_start time.
        meeting_start = max(arrival_time, meeting["avail_start"])
        meeting_end = meeting_start + meeting["min_duration"]
        
        # Check if meeting ends before meeting's avail_end.
        if meeting_end > meeting["avail_end"]:
            return False, None, None  # Not feasible
        
        # Append meeting event
        schedule.append({
            "action": "meet",
            "location": meeting["location"],
            "person": meeting["person"],
            "start_time": minutes_to_time(meeting_start),
            "end_time": minutes_to_time(meeting_end)
        })
        # Update current time & location for next meeting
        current_time = meeting_end
        current_location = meeting["location"]
    
    return True, schedule, current_time

# We try all permutations of the meetings and select the best schedule that maximizes number of meetings.
best_schedule = None
max_meetings = 0
best_finish_time = None

# We'll consider all subsets of meetings (by trying all permutations of full set and then later filtering out meetings that fail).
# Since we want to maximize number of friends met, we try all orders with length from len(meetings) down to 1.
from itertools import combinations

for r in range(len(meetings), 0, -1):
    for subset in combinations(meetings, r):
        for order in permutations(subset):
            feasible, sched, finish_time = evaluate_schedule(order)
            if feasible:
                if r > max_meetings or (r == max_meetings and (best_finish_time is None or finish_time < best_finish_time)):
                    max_meetings = r
                    best_schedule = sched
                    best_finish_time = finish_time
    # If we found any schedule meeting r meetings, we break because we prefer maximum number.
    if max_meetings == r and best_schedule is not None:
        break

# Prepare output dictionary in the required JSON structure.
output = {"itinerary": best_schedule if best_schedule is not None else []}

# Print JSON output.
print(json.dumps(output, indent=2))
    
if __name__ == '__main__':
    pass