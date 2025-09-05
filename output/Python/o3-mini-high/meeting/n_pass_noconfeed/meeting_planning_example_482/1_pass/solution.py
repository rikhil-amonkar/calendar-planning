import json

def minutes_to_time_str(m):
    hour = m // 60
    minute = m % 60
    return f"{hour}:{minute:02d}"

# Travel times (in minutes)
travel_times = {
    ("Haight-Ashbury", "Mission District"): 11,
    ("Haight-Ashbury", "Bayview"): 18,
    ("Haight-Ashbury", "Pacific Heights"): 12,
    ("Haight-Ashbury", "Russian Hill"): 17,
    ("Haight-Ashbury", "Fisherman's Wharf"): 23,
    ("Mission District", "Haight-Ashbury"): 12,
    ("Mission District", "Bayview"): 15,
    ("Mission District", "Pacific Heights"): 16,
    ("Mission District", "Russian Hill"): 15,
    ("Mission District", "Fisherman's Wharf"): 22,
    ("Bayview", "Haight-Ashbury"): 19,
    ("Bayview", "Mission District"): 13,
    ("Bayview", "Pacific Heights"): 23,
    ("Bayview", "Russian Hill"): 23,
    ("Bayview", "Fisherman's Wharf"): 25,
    ("Pacific Heights", "Haight-Ashbury"): 11,
    ("Pacific Heights", "Mission District"): 15,
    ("Pacific Heights", "Bayview"): 22,
    ("Pacific Heights", "Russian Hill"): 7,
    ("Pacific Heights", "Fisherman's Wharf"): 13,
    ("Russian Hill", "Haight-Ashbury"): 17,
    ("Russian Hill", "Mission District"): 16,
    ("Russian Hill", "Bayview"): 23,
    ("Russian Hill", "Pacific Heights"): 7,
    ("Russian Hill", "Fisherman's Wharf"): 7,
    ("Fisherman's Wharf", "Haight-Ashbury"): 22,
    ("Fisherman's Wharf", "Mission District"): 22,
    ("Fisherman's Wharf", "Bayview"): 26,
    ("Fisherman's Wharf", "Pacific Heights"): 12,
    ("Fisherman's Wharf", "Russian Hill"): 7
}

# Friends with their meeting constraints.
# Times are stored as minutes since midnight.
friends = [
    {
        "name": "Stephanie",
        "location": "Mission District",
        "avail_start": 8 * 60 + 15,    # 8:15 AM -> 495 minutes
        "avail_end": 13 * 60 + 45,     # 13:45 -> 825 minutes
        "duration": 90
    },
    {
        "name": "Sandra",
        "location": "Bayview",
        "avail_start": 13 * 60,        # 13:00 -> 780 minutes
        "avail_end": 19 * 60 + 30,     # 19:30 -> 1170 minutes
        "duration": 15
    },
    {
        "name": "Richard",
        "location": "Pacific Heights",
        "avail_start": 7 * 60 + 15,    # 7:15 -> 435 minutes
        "avail_end": 10 * 60 + 15,     # 10:15 -> 615 minutes
        "duration": 75
    },
    {
        "name": "Brian",
        "location": "Russian Hill",
        "avail_start": 12 * 60 + 15,   # 12:15 -> 735 minutes
        "avail_end": 16 * 60,          # 16:00 -> 960 minutes
        "duration": 120
    },
    {
        "name": "Jason",
        "location": "Fisherman's Wharf",
        "avail_start": 8 * 60 + 30,    # 8:30 -> 510 minutes
        "avail_end": 17 * 60 + 45,     # 17:45 -> 1065 minutes
        "duration": 60
    }
]

best_schedule = []
best_count = 0

def search_schedule(current_loc, current_time, schedule, remaining_friends):
    global best_schedule, best_count
    if len(schedule) > best_count:
        best_count = len(schedule)
        best_schedule = schedule.copy()
    for i, friend in enumerate(remaining_friends):
        # Get travel time from current location to friend's location
        key = (current_loc, friend["location"])
        if key not in travel_times:
            continue
        travel = travel_times[key]
        arrival_time = current_time + travel
        # The meeting can only start when the friend is available.
        start_meeting = max(arrival_time, friend["avail_start"])
        end_meeting = start_meeting + friend["duration"]
        if end_meeting <= friend["avail_end"]:
            meeting = {
                "action": "meet",
                "location": friend["location"],
                "person": friend["name"],
                "start_time": minutes_to_time_str(start_meeting),
                "end_time": minutes_to_time_str(end_meeting)
            }
            new_schedule = schedule + [meeting]
            new_remaining = remaining_friends[:i] + remaining_friends[i+1:]
            search_schedule(friend["location"], end_meeting, new_schedule, new_remaining)

# Starting point: You arrive at Haight-Ashbury at 9:00 AM (540 minutes).
start_location = "Haight-Ashbury"
start_time = 9 * 60  # 9:00 AM -> 540 minutes

search_schedule(start_location, start_time, [], friends)

result = {"itinerary": best_schedule}
print(json.dumps(result, indent=2))