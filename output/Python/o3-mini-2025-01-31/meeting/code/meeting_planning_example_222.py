#!/usr/bin/env python3
import json
import itertools

def time_to_str(t):
    # t in minutes since midnight; format as H:MM with no leading zero for hours
    hours = t // 60
    minutes = t % 60
    return f"{hours}:{minutes:02d}"

# Define travel times in minutes between locations
travel_times = {
    ("Nob Hill", "North Beach"): 8,
    ("Nob Hill", "Fisherman's Wharf"): 11,
    ("Nob Hill", "Bayview"): 19,
    ("North Beach", "Nob Hill"): 7,
    ("North Beach", "Fisherman's Wharf"): 5,
    ("North Beach", "Bayview"): 22,
    ("Fisherman's Wharf", "Nob Hill"): 11,
    ("Fisherman's Wharf", "North Beach"): 6,
    ("Fisherman's Wharf", "Bayview"): 26,
    ("Bayview", "Nob Hill"): 20,
    ("Bayview", "North Beach"): 21,
    ("Bayview", "Fisherman's Wharf"): 25,
}

def get_travel_time(origin, destination):
    return travel_times.get((origin, destination), float('inf'))

# Define the friends meeting constraints.
# Times are stored in minutes after midnight.
friends = {
    "Helen": {
        "location": "North Beach",
        "avail_start": 7 * 60,         # 7:00 AM -> 420 minutes
        "avail_end": 16 * 60 + 45,       # 16:45 -> 1005 minutes
        "min_duration": 120
    },
    "Kimberly": {
        "location": "Fisherman's Wharf",
        "avail_start": 16 * 60 + 30,     # 16:30 -> 990 minutes
        "avail_end": 21 * 60,            # 21:00 -> 1260 minutes
        "min_duration": 45
    },
    "Patricia": {
        "location": "Bayview",
        "avail_start": 18 * 60,          # 18:00 -> 1080 minutes
        "avail_end": 21 * 60 + 15,       # 21:15 -> 1275 minutes
        "min_duration": 120
    }
}

# Starting parameters
start_location = "Nob Hill"
start_time = 9 * 60  # 9:00 AM -> 540 minutes

def simulate_schedule(order):
    current_time = start_time
    current_location = start_location
    schedule = []
    
    for friend_name in order:
        friend = friends[friend_name]
        destination = friend["location"]
        travel = get_travel_time(current_location, destination)
        arrival_time = current_time + travel
        # The meeting can only start when the friend is available.
        meeting_start = max(arrival_time, friend["avail_start"])
        meeting_end = meeting_start + friend["min_duration"]
        # Check if meeting can finish before friend leaves
        if meeting_end > friend["avail_end"]:
            return None  # schedule not feasible
        # Append meeting details
        schedule.append({
            "action": "meet",
            "location": destination,
            "person": friend_name,
            "start_time": time_to_str(meeting_start),
            "end_time": time_to_str(meeting_end)
        })
        # Update time and location
        current_time = meeting_end
        current_location = destination
    return schedule

best_schedule = None
best_count = 0

# Try every permutation of friends and select the one that schedules the maximum meetings.
for order in itertools.permutations(friends.keys()):
    sched = simulate_schedule(order)
    if sched is not None:
        if len(sched) > best_count:
            best_schedule = sched
            best_count = len(sched)

# Create the final JSON structure
result = {"itinerary": best_schedule if best_schedule is not None else []}

# Output the result as JSON
print(json.dumps(result))