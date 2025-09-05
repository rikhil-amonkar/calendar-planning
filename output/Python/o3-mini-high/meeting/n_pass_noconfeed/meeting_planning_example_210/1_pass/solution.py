import json
import itertools

def minutes_to_time(mins):
    hours = mins // 60
    minutes = mins % 60
    return f"{hours}:{minutes:02d}"

# Travel times (in minutes) between locations
travel_times = {
    ("Fisherman's Wharf", "Presidio"): 17,
    ("Fisherman's Wharf", "Richmond District"): 18,
    ("Fisherman's Wharf", "Financial District"): 11,
    ("Presidio", "Fisherman's Wharf"): 19,
    ("Presidio", "Richmond District"): 7,
    ("Presidio", "Financial District"): 23,
    ("Richmond District", "Fisherman's Wharf"): 18,
    ("Richmond District", "Presidio"): 7,
    ("Richmond District", "Financial District"): 22,
    ("Financial District", "Fisherman's Wharf"): 10,
    ("Financial District", "Presidio"): 22,
    ("Financial District", "Richmond District"): 21,
}

# Meeting constraints for each friend
# Times are represented as minutes from midnight.
# Emily: at Presidio from 16:15 (975) to 21:00 (1260), needs 105 minutes.
# Joseph: at Richmond District from 17:15 (1035) to 22:00 (1320), needs 120 minutes.
# Melissa: at Financial District from 15:45 (945) to 21:45 (1305), needs 75 minutes.
friends = [
    {
        "name": "Emily",
        "location": "Presidio",
        "avail_start": 16 * 60 + 15,  # 16:15 -> 975 minutes
        "avail_end": 21 * 60,         # 21:00 -> 1260 minutes
        "min_duration": 105
    },
    {
        "name": "Joseph",
        "location": "Richmond District",
        "avail_start": 17 * 60 + 15,  # 17:15 -> 1035 minutes
        "avail_end": 22 * 60,         # 22:00 -> 1320 minutes
        "min_duration": 120
    },
    {
        "name": "Melissa",
        "location": "Financial District",
        "avail_start": 15 * 60 + 45,  # 15:45 -> 945 minutes
        "avail_end": 21 * 60 + 45,    # 21:45 -> 1305 minutes
        "min_duration": 75
    }
]

# Starting parameters: You arrive at Fisherman's Wharf at 9:00 AM.
start_location = "Fisherman's Wharf"
start_time = 9 * 60  # 9:00 -> 540 minutes

best_schedule = None
best_finish_time = float('inf')

# Try all possible orders to meet the friends.
for order in itertools.permutations(friends):
    current_time = start_time
    current_location = start_location
    schedule = []
    valid = True
    
    for friend in order:
        # Get travel time from current location to friend's location.
        travel_key = (current_location, friend["location"])
        travel = travel_times.get(travel_key, float('inf'))
        arrival_time = current_time + travel
        
        # You can only start meeting when the friend is available.
        meeting_start = max(arrival_time, friend["avail_start"])
        meeting_end = meeting_start + friend["min_duration"]
        
        # Check if meeting can be held within the friend's available window.
        if meeting_end > friend["avail_end"]:
            valid = False
            break
        
        # Append this meeting event to the schedule.
        schedule.append({
            "action": "meet",
            "location": friend["location"],
            "person": friend["name"],
            "start_time": minutes_to_time(meeting_start),
            "end_time": minutes_to_time(meeting_end)
        })
        
        # Update the current time and location.
        current_time = meeting_end
        current_location = friend["location"]
    
    # If this order produced a valid schedule, check its finishing time.
    if valid and current_time < best_finish_time:
        best_finish_time = current_time
        best_schedule = schedule

# Prepare the result as a JSON-formatted dictionary.
result = {
    "itinerary": best_schedule if best_schedule is not None else []
}

print(json.dumps(result, indent=2))