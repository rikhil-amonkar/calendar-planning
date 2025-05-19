#!/usr/bin/env python3
import json
import itertools

# Helper function: convert minutes from midnight to H:MM (24-hour) string (no leading zero for hour)
def minutes_to_time(minutes):
    hour = minutes // 60
    minute = minutes % 60
    return f"{hour}:{minute:02d}"

# Travel times (in minutes) as provided; keys are (from, to)
travel_times = {
    ("Financial District", "Russian Hill"): 10,
    ("Financial District", "Sunset District"): 31,
    ("Financial District", "North Beach"): 7,
    ("Financial District", "The Castro"): 23,
    ("Financial District", "Golden Gate Park"): 23,
    
    ("Russian Hill", "Financial District"): 11,
    ("Russian Hill", "Sunset District"): 23,
    ("Russian Hill", "North Beach"): 5,
    ("Russian Hill", "The Castro"): 21,
    ("Russian Hill", "Golden Gate Park"): 21,
    
    ("Sunset District", "Financial District"): 30,
    ("Sunset District", "Russian Hill"): 24,
    ("Sunset District", "North Beach"): 29,
    ("Sunset District", "The Castro"): 17,
    ("Sunset District", "Golden Gate Park"): 11,
    
    ("North Beach", "Financial District"): 8,
    ("North Beach", "Russian Hill"): 5,
    ("North Beach", "Sunset District"): 27,
    ("North Beach", "The Castro"): 20,
    ("North Beach", "Golden Gate Park"): 22,
    
    ("The Castro", "Financial District"): 20,
    ("The Castro", "Russian Hill"): 18,
    ("The Castro", "Sunset District"): 17,
    ("The Castro", "North Beach"): 20,
    ("The Castro", "Golden Gate Park"): 11,
    
    ("Golden Gate Park", "Financial District"): 26,
    ("Golden Gate Park", "Russian Hill"): 19,
    ("Golden Gate Park", "Sunset District"): 10,
    ("Golden Gate Park", "North Beach"): 24,
    ("Golden Gate Park", "The Castro"): 13,
}

# Meeting data for each friend:
# Times are in minutes from midnight.
# Patricia: available at Sunset District from 9:15 (555) to 22:00 (1320), minimum meeting duration 60 minutes.
# Ronald: available at Russian Hill from 13:45 (825) to 17:15 (1035), min duration 105.
# Laura: available at North Beach from 12:30 (750) to 12:45 (765), min duration 15.
# Emily: available at The Castro from 16:15 (975) to 18:30 (1110), min 60.
# Mary: available at Golden Gate Park from 15:00 (900) to 16:30 (990), min 60.
meetings = {
    "Patricia": {
        "location": "Sunset District",
        "avail_start": 555,
        "avail_end": 1320,
        "duration": 60,
    },
    "Ronald": {
        "location": "Russian Hill",
        "avail_start": 825,
        "avail_end": 1035,
        "duration": 105,
    },
    "Laura": {
        "location": "North Beach",
        "avail_start": 750,
        "avail_end": 765,
        "duration": 15,
    },
    "Emily": {
        "location": "The Castro",
        "avail_start": 975,
        "avail_end": 1110,
        "duration": 60,
    },
    "Mary": {
        "location": "Golden Gate Park",
        "avail_start": 900,
        "avail_end": 990,
        "duration": 60,
    },
}

# Starting parameters:
start_location = "Financial District"
start_time = 540  # 9:00 AM is 540 minutes from midnight

# We'll build the schedule in three segments:
# 1. Pre-Laura meetings: We can schedule Patricia (and possibly others, but Patricia is the only one available early).
# 2. The fixed appointment: Laura at North Beach (time fixed 12:30-12:45).
# 3. Post-Laura meetings: among {Ronald, Mary, Emily} we choose an ordering that yields the maximum number of meetings.

# For simplicity, we assume that a meeting is only possible if:
#   meeting_start = max(arrival_time, avail_start), and meeting_end = meeting_start + duration, and must satisfy meeting_end <= avail_end.
#   We also add travel times between consecutively scheduled appointments.

# Schedule segment 1: Pre-Laura.
itinerary = []

current_location = start_location
current_time = start_time

# We want to meet Patricia early.
friend = "Patricia"
friend_data = meetings[friend]
# Travel time from start location to Patricia's meeting location:
tt = travel_times[(current_location, friend_data["location"])]
arrival_time = current_time + tt
# Meeting cannot start before available start; so meeting start is:
meeting_start = max(arrival_time, friend_data["avail_start"])
meeting_end = meeting_start + friend_data["duration"]
# Check feasibility (should be feasible as 9:31 to 10:31):
if meeting_end <= friend_data["avail_end"]:
    itinerary.append({
        "action": "meet",
        "location": friend_data["location"],
        "person": friend,
        "start_time": minutes_to_time(meeting_start),
        "end_time": minutes_to_time(meeting_end)
    })
    current_location = friend_data["location"]
    current_time = meeting_end

# Now we need to schedule the fixed Laura meeting.
# We must travel to North Beach from current location.
tt = travel_times[(current_location, meetings["Laura"]["location"])]
arrival_time = current_time + tt
# Laura's available window is fixed (750 to 765). We assume we wait if arriving early.
meeting_start = max(arrival_time, meetings["Laura"]["avail_start"])
meeting_end = meeting_start + meetings["Laura"]["duration"]
# Only schedule if it fits in Laura's window.
if meeting_end <= meetings["Laura"]["avail_end"]:
    itinerary.append({
        "action": "meet",
        "location": meetings["Laura"]["location"],
        "person": "Laura",
        "start_time": minutes_to_time(meeting_start),
        "end_time": minutes_to_time(meeting_end)
    })
    current_location = meetings["Laura"]["location"]
    current_time = meeting_end
else:
    # If not feasible, abort.
    print(json.dumps({"itinerary": []}))
    exit(0)

# Post-Laura meetings: choose maximum feasible subset from {Ronald, Mary, Emily}
post_candidates = ["Ronald", "Mary", "Emily"]

def simulate_schedule(order, start_location, start_time):
    """Given an ordering of friends (list of names), simulate and return schedule and finish time.
       Returns (schedule_list, final_time) if feasible, else (None, None)."""
    sched = []
    cur_loc = start_location
    cur_time = start_time
    for friend in order:
        data = meetings[friend]
        # Determine travel time from current location to friend's location.
        tt = travel_times.get((cur_loc, data["location"]))
        if tt is None:
            # Cannot travel if not defined.
            return None, None
        arrival = cur_time + tt
        m_start = max(arrival, data["avail_start"])
        m_end = m_start + data["duration"]
        if m_end > data["avail_end"]:
            return None, None
        sched.append({
            "action": "meet",
            "location": data["location"],
            "person": friend,
            "start_time": m_start,
            "end_time": m_end
        })
        cur_loc = data["location"]
        cur_time = m_end
    return sched, cur_time

# We'll search over all permutations (of all lengths) of post_candidates to find the ordering with maximum meetings.
best_order = []
best_sched = []
max_meetings = 0
best_finish = None

# We consider non-empty subsets (or even empty, but we want maximum meetings).
for r in range(1, len(post_candidates)+1):
    for order in itertools.permutations(post_candidates, r):
        sched, finish = simulate_schedule(order, current_location, current_time)
        if sched is not None:
            if len(order) > max_meetings:
                max_meetings = len(order)
                best_order = order
                best_sched = sched
                best_finish = finish
            # As tie-breaker, choose the schedule that finishes earlier.
            elif len(order) == max_meetings and best_finish is not None and finish < best_finish:
                best_order = order
                best_sched = sched
                best_finish = finish

# Append the post-Laura schedule (if any) to itinerary.
if best_sched:
    # best_sched contains meeting times in minute integers; convert times to proper string format.
    for meet in best_sched:
        meet["start_time"] = minutes_to_time(meet["start_time"])
        meet["end_time"] = minutes_to_time(meet["end_time"])
        itinerary.append(meet)

# Our final itinerary is what we managed to schedule.
result = {"itinerary": itinerary}

# Output the JSON-formatted result.
print(json.dumps(result, indent=2))