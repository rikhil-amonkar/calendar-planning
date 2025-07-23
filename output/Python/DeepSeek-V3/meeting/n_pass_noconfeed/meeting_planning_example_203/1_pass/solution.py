import json
from itertools import permutations

def time_to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Travel times in minutes (from: {to: time})
travel_times = {
    "Financial District": {
        "Fisherman's Wharf": 10,
        "Pacific Heights": 13,
        "Mission District": 17
    },
    "Fisherman's Wharf": {
        "Financial District": 11,
        "Pacific Heights": 12,
        "Mission District": 22
    },
    "Pacific Heights": {
        "Financial District": 13,
        "Fisherman's Wharf": 13,
        "Mission District": 15
    },
    "Mission District": {
        "Financial District": 17,
        "Fisherman's Wharf": 22,
        "Pacific Heights": 16
    }
}

# Constraints
start_location = "Financial District"
start_time = time_to_minutes("9:00")

friends = {
    "David": {
        "location": "Fisherman's Wharf",
        "available_start": time_to_minutes("10:45"),
        "available_end": time_to_minutes("15:30"),
        "min_duration": 15
    },
    "Timothy": {
        "location": "Pacific Heights",
        "available_start": time_to_minutes("9:00"),
        "available_end": time_to_minutes("15:30"),
        "min_duration": 75
    },
    "Robert": {
        "location": "Mission District",
        "available_start": time_to_minutes("12:15"),
        "available_end": time_to_minutes("19:45"),
        "min_duration": 90
    }
}

def calculate_schedule(order):
    current_time = start_time
    current_location = start_location
    schedule = []
    possible = True
    
    for friend_name in order:
        friend = friends[friend_name]
        location = friend["location"]
        
        # Travel time
        travel_time = travel_times[current_location][location]
        arrival_time = current_time + travel_time
        
        # Check if we can meet
        meeting_start = max(arrival_time, friend["available_start"])
        meeting_end = meeting_start + friend["min_duration"]
        
        if meeting_end > friend["available_end"]:
            possible = False
            break
        
        schedule.append({
            "action": "meet",
            "location": location,
            "person": friend_name,
            "start_time": minutes_to_time(meeting_start),
            "end_time": minutes_to_time(meeting_end)
        })
        
        current_time = meeting_end
        current_location = location
    
    return schedule if possible else None

# Try all possible orders
best_schedule = None
best_friends_met = 0

for order in permutations(friends.keys()):
    schedule = calculate_schedule(order)
    if schedule and len(schedule) > best_friends_met:
        best_schedule = schedule
        best_friends_met = len(schedule)

# Output the best schedule
output = {
    "itinerary": best_schedule if best_schedule else []
}

print(json.dumps(output, indent=2))