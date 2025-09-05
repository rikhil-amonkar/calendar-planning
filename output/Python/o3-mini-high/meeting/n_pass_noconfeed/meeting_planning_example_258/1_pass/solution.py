import json
import itertools

def time_to_minutes(t):
    # t is in format "H:MM", e.g., "9:00" or "13:30"
    h, m = t.split(':')
    return int(h) * 60 + int(m)

def minutes_to_time(m):
    h = m // 60
    min_part = m % 60
    return f"{h}:{min_part:02d}"

# Travel times in minutes between locations.
travel_times = {
    "Embarcadero": {
        "Presidio": 20,
        "Richmond District": 21,
        "Fisherman's Wharf": 6
    },
    "Presidio": {
        "Embarcadero": 20,
        "Richmond District": 7,
        "Fisherman's Wharf": 19
    },
    "Richmond District": {
        "Embarcadero": 19,
        "Presidio": 7,
        "Fisherman's Wharf": 18
    },
    "Fisherman's Wharf": {
        "Embarcadero": 8,
        "Presidio": 17,
        "Richmond District": 18
    }
}

# Meeting constraints for each friend.
meetings = {
    "Betty": {
        "location": "Presidio",
        "available_start": "10:15",
        "available_end": "21:30",  # 9:30 PM
        "min_duration": 45
    },
    "David": {
        "location": "Richmond District",
        "available_start": "13:00",  # 1:00 PM
        "available_end": "20:15",    # 8:15 PM
        "min_duration": 90
    },
    "Barbara": {
        "location": "Fisherman's Wharf",
        "available_start": "9:15",
        "available_end": "20:15",    # 8:15 PM
        "min_duration": 120
    }
}

# Starting conditions
initial_location = "Embarcadero"
start_time_str = "9:00"
initial_time = time_to_minutes(start_time_str)

# We want to meet as many friends as possible.
# We'll consider every permutation of the three friends and pick the one with the earliest finish time.
best_itinerary = None
best_finish_time = float('inf')
best_meet_count = 0

# Iterate through all possible meeting orders
for perm in itertools.permutations(meetings.keys()):
    current_time = initial_time
    current_location = initial_location
    itinerary = []
    valid_schedule = True
    
    for friend in perm:
        friend_info = meetings[friend]
        destination = friend_info["location"]
        # Get travel time from current location to destination
        travel = travel_times[current_location][destination]
        arrival_time = current_time + travel
        
        friend_available_start = time_to_minutes(friend_info["available_start"])
        friend_available_end = time_to_minutes(friend_info["available_end"])
        
        # Meeting can't start before arrival or before friend's available start.
        meeting_start = max(arrival_time, friend_available_start)
        meeting_finish = meeting_start + friend_info["min_duration"]
        
        # Check if the meeting can be completed within friend's available window.
        if meeting_finish > friend_available_end:
            valid_schedule = False
            break
        
        # Add the meeting event to the itinerary.
        itinerary.append({
            "action": "meet",
            "location": destination,
            "person": friend,
            "start_time": minutes_to_time(meeting_start),
            "end_time": minutes_to_time(meeting_finish)
        })
        
        # Update current state for next meeting.
        current_time = meeting_finish
        current_location = destination
    
    if valid_schedule:
        meet_count = len(itinerary)
        # We want to maximize the number of meetings, and as a tie-breaker choose the earliest finish.
        if meet_count > best_meet_count or (meet_count == best_meet_count and current_time < best_finish_time):
            best_meet_count = meet_count
            best_finish_time = current_time
            best_itinerary = itinerary

# Prepare the output JSON object
output = {"itinerary": best_itinerary if best_itinerary is not None else []}

print(json.dumps(output, indent=2))