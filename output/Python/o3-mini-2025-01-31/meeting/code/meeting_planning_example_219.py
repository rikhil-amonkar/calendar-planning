#!/usr/bin/env python3
import json
import itertools

# Helper functions to convert time to minutes and back.
def time_to_minutes(time_str):
    # Expects format "H:MM" in 24-hour format (e.g., "9:00" or "13:30")
    parts = time_str.split(":")
    return int(parts[0]) * 60 + int(parts[1])

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

# Define travel times between locations (in minutes)
# Keys are tuples (origin, destination)
travel_times = {
    ("The Castro", "Alamo Square"): 8,
    ("The Castro", "Union Square"): 19,
    ("The Castro", "Chinatown"): 20,
    ("Alamo Square", "The Castro"): 8,
    ("Alamo Square", "Union Square"): 14,
    ("Alamo Square", "Chinatown"): 16,
    ("Union Square", "The Castro"): 19,
    ("Union Square", "Alamo Square"): 15,
    ("Union Square", "Chinatown"): 7,
    ("Chinatown", "The Castro"): 22,
    ("Chinatown", "Alamo Square"): 17,
    ("Chinatown", "Union Square"): 7,
}

# Define friend meeting constraints
friends = {
    "Emily": {
        "location": "Alamo Square",
        "available_start": time_to_minutes("11:45"),
        "available_end": time_to_minutes("15:15"),
        "min_duration": 105
    },
    "Barbara": {
        "location": "Union Square",
        "available_start": time_to_minutes("16:45"),
        "available_end": time_to_minutes("18:15"),
        "min_duration": 60
    },
    "William": {
        "location": "Chinatown",
        "available_start": time_to_minutes("17:15"),
        "available_end": time_to_minutes("19:00"),
        "min_duration": 105
    }
}

# Starting location and time
start_location = "The Castro"
start_time = time_to_minutes("9:00")

# We'll search across all possible orders (subsets) of friends
# Our goal is to maximize the number of friends met; if tie, maximize total meeting minutes.
best_schedule = None
best_score = (-1, -1)  # (number of meetings, total meeting minutes)

# Get all non-empty subsets of friends' names
all_friends = list(friends.keys())
for r in range(1, len(all_friends) + 1):
    for subset in itertools.permutations(all_friends, r):
        current_time = start_time
        current_location = start_location
        schedule = []
        valid = True
        total_meeting_time = 0
        
        for person in subset:
            friend = friends[person]
            dest = friend["location"]
            # Determine travel time from current_location to dest.
            # If no direct entry, we assume the reverse if available.
            travel_key = (current_location, dest)
            if travel_key not in travel_times:
                valid = False
                break
            travel_duration = travel_times[travel_key]
            # Arrival time at destination:
            arrival_time = current_time + travel_duration
            # Meeting can only start after friend's available_start:
            meeting_start = max(arrival_time, friend["available_start"])
            meeting_end = meeting_start + friend["min_duration"]
            # If meeting would finish after the friend's available_end, schedule is invalid.
            if meeting_end > friend["available_end"]:
                valid = False
                break
            # Append meeting event details
            schedule.append({
                "action": "meet",
                "location": dest,
                "person": person,
                "start_time": minutes_to_time(meeting_start),
                "end_time": minutes_to_time(meeting_end)
            })
            total_meeting_time += friend["min_duration"]
            # Update current time and location
            current_time = meeting_end
            current_location = dest
        
        if valid:
            score = (len(schedule), total_meeting_time)
            # Choose schedule with more meetings; if tie, with higher total meeting minutes.
            if score > best_score:
                best_score = score
                best_schedule = schedule

# If no valid schedule was found, result is an empty itinerary.
result = {"itinerary": best_schedule if best_schedule is not None else []}

# Output the JSON-formatted result
print(json.dumps(result, indent=2))
                        
if __name__ == "__main__":
    pass