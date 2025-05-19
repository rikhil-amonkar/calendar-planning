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
initial_location = "Haight-Ashbury"
initial_time = "9:00"

# Friends' availability
friends = [
    {
        "name": "Sarah",
        "location": "Fisherman's Wharf",
        "start": "14:45",
        "end": "17:30",
        "duration": 105
    },
    {
        "name": "Mary",
        "location": "Richmond District",
        "start": "13:00",
        "end": "19:15",
        "duration": 75
    },
    {
        "name": "Helen",
        "location": "Mission District",
        "start": "21:45",
        "end": "22:30",
        "duration": 30
    },
    {
        "name": "Thomas",
        "location": "Bayview",
        "start": "15:15",
        "end": "18:45",
        "duration": 120
    }
]

# Travel times in minutes
travel_times = {
    "Haight-Ashbury": {
        "Fisherman's Wharf": 23,
        "Richmond District": 10,
        "Mission District": 11,
        "Bayview": 18
    },
    "Fisherman's Wharf": {
        "Haight-Ashbury": 22,
        "Richmond District": 18,
        "Mission District": 22,
        "Bayview": 26
    },
    "Richmond District": {
        "Haight-Ashbury": 10,
        "Fisherman's Wharf": 18,
        "Mission District": 20,
        "Bayview": 26
    },
    "Mission District": {
        "Haight-Ashbury": 12,
        "Fisherman's Wharf": 22,
        "Richmond District": 20,
        "Bayview": 15
    },
    "Bayview": {
        "Haight-Ashbury": 19,
        "Fisherman's Wharf": 25,
        "Richmond District": 25,
        "Mission District": 13
    }
}

def calculate_schedule(order):
    current_location = initial_location
    current_time = time_to_minutes(initial_time)
    schedule = []
    met_friends = set()
    
    for friend_name in order:
        friend = next(f for f in friends if f["name"] == friend_name)
        
        # Travel to friend's location
        travel_time = travel_times[current_location][friend["location"]]
        arrival_time = current_time + travel_time
        
        # Check if we can meet this friend
        friend_start = time_to_minutes(friend["start"])
        friend_end = time_to_minutes(friend["end"])
        
        # Calculate meeting window
        meeting_start = max(arrival_time, friend_start)
        meeting_end = min(meeting_start + friend["duration"], friend_end)
        
        if meeting_end - meeting_start >= friend["duration"]:
            schedule.append({
                "action": "meet",
                "location": friend["location"],
                "person": friend["name"],
                "start_time": minutes_to_time(meeting_start),
                "end_time": minutes_to_time(meeting_end)
            })
            met_friends.add(friend_name)
            current_time = meeting_end
            current_location = friend["location"]
    
    # Meet Helen last if possible
    helen = next(f for f in friends if f["name"] == "Helen")
    if "Helen" not in met_friends:
        travel_time = travel_times[current_location][helen["location"]]
        arrival_time = current_time + travel_time
        helen_start = time_to_minutes(helen["start"])
        helen_end = time_to_minutes(helen["end"])
        
        meeting_start = max(arrival_time, helen_start)
        meeting_end = min(meeting_start + helen["duration"], helen_end)
        
        if meeting_end - meeting_start >= helen["duration"]:
            schedule.append({
                "action": "meet",
                "location": helen["location"],
                "person": helen["name"],
                "start_time": minutes_to_time(meeting_start),
                "end_time": minutes_to_time(meeting_end)
            })
            met_friends.add("Helen")
    
    return schedule, len(met_friends)

# Generate all possible orders of meeting friends (excluding Helen)
friend_names = [f["name"] for f in friends if f["name"] != "Helen"]
best_schedule = []
max_met = 0

# Try all permutations of the first three friends
for perm in permutations(friend_names):
    schedule, num_met = calculate_schedule(perm)
    if num_met > max_met or (num_met == max_met and len(schedule) < len(best_schedule)):
        best_schedule = schedule
        max_met = num_met

# Output the best schedule
result = {
    "itinerary": best_schedule
}

print(json.dumps(result, indent=2))