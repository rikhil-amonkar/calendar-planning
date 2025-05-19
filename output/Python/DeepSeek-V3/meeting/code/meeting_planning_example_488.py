import json
from itertools import permutations

def time_to_minutes(time_str):
    hours, minutes = map(int, time_str.split(':'))
    return hours * 60 + minutes

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

# Input parameters
start_location = "Pacific Heights"
start_time = "9:00"

friends = [
    {"name": "Ronald", "location": "Nob Hill", "available_start": "10:00", "available_end": "17:00", "min_duration": 105},
    {"name": "Sarah", "location": "Russian Hill", "available_start": "7:15", "available_end": "9:30", "min_duration": 45},
    {"name": "Helen", "location": "The Castro", "available_start": "13:30", "available_end": "17:00", "min_duration": 120},
    {"name": "Joshua", "location": "Sunset District", "available_start": "14:15", "available_end": "19:30", "min_duration": 90},
    {"name": "Margaret", "location": "Haight-Ashbury", "available_start": "10:15", "available_end": "22:00", "min_duration": 60}
]

# Travel times in minutes (from -> to)
travel_times = {
    "Pacific Heights": {
        "Nob Hill": 8,
        "Russian Hill": 7,
        "The Castro": 16,
        "Sunset District": 21,
        "Haight-Ashbury": 11
    },
    "Nob Hill": {
        "Pacific Heights": 8,
        "Russian Hill": 5,
        "The Castro": 17,
        "Sunset District": 25,
        "Haight-Ashbury": 13
    },
    "Russian Hill": {
        "Pacific Heights": 7,
        "Nob Hill": 5,
        "The Castro": 21,
        "Sunset District": 23,
        "Haight-Ashbury": 17
    },
    "The Castro": {
        "Pacific Heights": 16,
        "Nob Hill": 16,
        "Russian Hill": 18,
        "Sunset District": 17,
        "Haight-Ashbury": 6
    },
    "Sunset District": {
        "Pacific Heights": 21,
        "Nob Hill": 27,
        "Russian Hill": 24,
        "The Castro": 17,
        "Haight-Ashbury": 15
    },
    "Haight-Ashbury": {
        "Pacific Heights": 12,
        "Nob Hill": 15,
        "Russian Hill": 17,
        "The Castro": 6,
        "Sunset District": 15
    }
}

def calculate_schedule(order):
    current_time = time_to_minutes(start_time)
    current_location = start_location
    schedule = []
    met_friends = set()
    
    for friend_name in order:
        friend = next(f for f in friends if f["name"] == friend_name)
        
        # Calculate travel time
        travel_time = travel_times[current_location][friend["location"]]
        arrival_time = current_time + travel_time
        
        # Check if we can meet this friend
        available_start = time_to_minutes(friend["available_start"])
        available_end = time_to_minutes(friend["available_end"])
        
        # Adjust meeting time to fit within availability
        meeting_start = max(arrival_time, available_start)
        meeting_end = meeting_start + friend["min_duration"]
        
        if meeting_end > available_end:
            return None  # Can't meet this friend with required duration
        
        # Add to schedule
        schedule.append({
            "action": "meet",
            "location": friend["location"],
            "person": friend["name"],
            "start_time": minutes_to_time(meeting_start),
            "end_time": minutes_to_time(meeting_end)
        })
        
        met_friends.add(friend["name"])
        current_time = meeting_end
        current_location = friend["location"]
    
    return schedule if len(met_friends) == len(order) else None

# Generate all possible meeting orders and find the best one
best_schedule = None
max_meetings = 0

# Try all possible permutations of friends (up to 5! = 120 possibilities)
for friend_order in permutations([f["name"] for f in friends]):
    schedule = calculate_schedule(friend_order)
    if schedule and len(schedule) > max_meetings:
        best_schedule = schedule
        max_meetings = len(schedule)
    elif schedule and len(schedule) == max_meetings:
        # Prefer schedules that end earlier
        if not best_schedule or time_to_minutes(schedule[-1]["end_time"]) < time_to_minutes(best_schedule[-1]["end_time"]):
            best_schedule = schedule

# Output the result
result = {"itinerary": best_schedule} if best_schedule else {"itinerary": []}
print(json.dumps(result, indent=2))