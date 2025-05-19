import json
from itertools import permutations

def time_to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Input parameters
initial_location = "Financial District"
initial_time = "9:00"

# Friend constraints
friends = [
    {
        "name": "David",
        "location": "Fisherman's Wharf",
        "available_start": "10:45",
        "available_end": "15:30",
        "min_duration": 15
    },
    {
        "name": "Timothy",
        "location": "Pacific Heights",
        "available_start": "9:00",
        "available_end": "15:30",
        "min_duration": 75
    },
    {
        "name": "Robert",
        "location": "Mission District",
        "available_start": "12:15",
        "available_end": "19:45",
        "min_duration": 90
    }
]

# Travel times in minutes
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

def calculate_schedule(order):
    current_location = initial_location
    current_time = time_to_minutes(initial_time)
    schedule = []
    met_friends = set()
    
    for friend_name in order:
        friend = next(f for f in friends if f["name"] == friend_name)
        if friend["name"] in met_friends:
            continue
        
        travel_time = travel_times[current_location][friend["location"]]
        arrival_time = current_time + travel_time
        available_start = time_to_minutes(friend["available_start"])
        available_end = time_to_minutes(friend["available_end"])
        
        start_time = max(arrival_time, available_start)
        end_time = start_time + friend["min_duration"]
        
        if end_time > available_end:
            return None
        
        schedule.append({
            "action": "meet",
            "location": friend["location"],
            "person": friend["name"],
            "start_time": minutes_to_time(start_time),
            "end_time": minutes_to_time(end_time)
        })
        
        current_location = friend["location"]
        current_time = end_time
        met_friends.add(friend["name"])
    
    return schedule

best_schedule = None
best_meetings = 0

# Try all possible meeting orders
for order in permutations(["David", "Timothy", "Robert"]):
    met_friends = set()
    schedule = calculate_schedule(order)
    if schedule and len(schedule) > best_meetings:
        best_schedule = schedule
        best_meetings = len(schedule)
    elif schedule and len(schedule) == best_meetings:
        # Prefer schedules that meet more important friends first
        pass

if not best_schedule:
    # Try meeting just two friends
    for order in permutations(["David", "Timothy", "Robert"], 2):
        met_friends = set()
        schedule = calculate_schedule(order)
        if schedule and len(schedule) > best_meetings:
            best_schedule = schedule
            best_meetings = len(schedule)

# Output the best schedule found
result = {
    "itinerary": best_schedule
}

print(json.dumps(result, indent=2))