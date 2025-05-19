import json
from itertools import permutations

# Travel times dictionary (from -> to -> minutes)
travel_times = {
    "Russian Hill": {
        "Sunset District": 23,
        "Union Square": 10,
        "Nob Hill": 5,
        "Marina District": 7,
        "Richmond District": 14,
        "Financial District": 11,
        "Embarcadero": 8,
        "The Castro": 21,
        "Alamo Square": 15,
        "Presidio": 14
    },
    "Sunset District": {
        "Russian Hill": 24,
        "Union Square": 30,
        "Nob Hill": 27,
        "Marina District": 21,
        "Richmond District": 12,
        "Financial District": 30,
        "Embarcadero": 30,
        "The Castro": 17,
        "Alamo Square": 17,
        "Presidio": 16
    },
    "Union Square": {
        "Russian Hill": 13,
        "Sunset District": 27,
        "Nob Hill": 9,
        "Marina District": 18,
        "Richmond District": 20,
        "Financial District": 9,
        "Embarcadero": 11,
        "The Castro": 17,
        "Alamo Square": 15,
        "Presidio": 24
    },
    "Nob Hill": {
        "Russian Hill": 5,
        "Sunset District": 24,
        "Union Square": 7,
        "Marina District": 11,
        "Richmond District": 14,
        "Financial District": 9,
        "Embarcadero": 9,
        "The Castro": 17,
        "Alamo Square": 11,
        "Presidio": 17
    },
    "Marina District": {
        "Russian Hill": 8,
        "Sunset District": 19,
        "Union Square": 16,
        "Nob Hill": 12,
        "Richmond District": 11,
        "Financial District": 17,
        "Embarcadero": 14,
        "The Castro": 22,
        "Alamo Square": 15,
        "Presidio": 10
    },
    "Richmond District": {
        "Russian Hill": 13,
        "Sunset District": 11,
        "Union Square": 21,
        "Nob Hill": 17,
        "Marina District": 9,
        "Financial District": 22,
        "Embarcadero": 19,
        "The Castro": 16,
        "Alamo Square": 13,
        "Presidio": 7
    },
    "Financial District": {
        "Russian Hill": 11,
        "Sunset District": 30,
        "Union Square": 9,
        "Nob Hill": 8,
        "Marina District": 15,
        "Richmond District": 21,
        "Embarcadero": 4,
        "The Castro": 20,
        "Alamo Square": 17,
        "Presidio": 22
    },
    "Embarcadero": {
        "Russian Hill": 8,
        "Sunset District": 30,
        "Union Square": 10,
        "Nob Hill": 10,
        "Marina District": 12,
        "Richmond District": 21,
        "Financial District": 5,
        "The Castro": 25,
        "Alamo Square": 19,
        "Presidio": 20
    },
    "The Castro": {
        "Russian Hill": 18,
        "Sunset District": 17,
        "Union Square": 19,
        "Nob Hill": 16,
        "Marina District": 21,
        "Richmond District": 16,
        "Financial District": 21,
        "Embarcadero": 22,
        "Alamo Square": 8,
        "Presidio": 20
    },
    "Alamo Square": {
        "Russian Hill": 13,
        "Sunset District": 16,
        "Union Square": 14,
        "Nob Hill": 11,
        "Marina District": 15,
        "Richmond District": 11,
        "Financial District": 17,
        "Embarcadero": 16,
        "The Castro": 8,
        "Presidio": 17
    },
    "Presidio": {
        "Russian Hill": 14,
        "Sunset District": 15,
        "Union Square": 22,
        "Nob Hill": 18,
        "Marina District": 11,
        "Richmond District": 7,
        "Financial District": 23,
        "Embarcadero": 20,
        "The Castro": 21,
        "Alamo Square": 19
    }
}

# Friend constraints
friends = [
    {"name": "David", "location": "Sunset District", "start": "9:15", "end": "22:00", "min_duration": 15},
    {"name": "Kenneth", "location": "Union Square", "start": "21:15", "end": "21:45", "min_duration": 15},
    {"name": "Patricia", "location": "Nob Hill", "start": "15:00", "end": "19:15", "min_duration": 120},
    {"name": "Mary", "location": "Marina District", "start": "14:45", "end": "16:45", "min_duration": 45},
    {"name": "Charles", "location": "Richmond District", "start": "17:15", "end": "21:00", "min_duration": 15},
    {"name": "Joshua", "location": "Financial District", "start": "14:30", "end": "17:15", "min_duration": 90},
    {"name": "Ronald", "location": "Embarcadero", "start": "18:15", "end": "20:45", "min_duration": 30},
    {"name": "George", "location": "The Castro", "start": "14:15", "end": "19:00", "min_duration": 105},
    {"name": "Kimberly", "location": "Alamo Square", "start": "9:00", "end": "14:30", "min_duration": 105},
    {"name": "William", "location": "Presidio", "start": "7:00", "end": "12:45", "min_duration": 60}
]

def time_to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Convert friend times to minutes
for friend in friends:
    friend["start_min"] = time_to_minutes(friend["start"])
    friend["end_min"] = time_to_minutes(friend["end"])

def calculate_schedule(order):
    current_location = "Russian Hill"
    current_time = time_to_minutes("9:00")
    schedule = []
    remaining_friends = friends.copy()
    
    for friend_name in order:
        friend = next(f for f in remaining_friends if f["name"] == friend_name)
        remaining_friends.remove(friend)
        
        # Calculate travel time
        travel_time = travel_times[current_location][friend["location"]]
        arrival_time = current_time + travel_time
        
        # Check if we can meet
        meeting_start = max(arrival_time, friend["start_min"])
        meeting_end = meeting_start + friend["min_duration"]
        
        if meeting_end > friend["end_min"]:
            return None  # Can't meet this friend
        
        # Add to schedule
        schedule.append({
            "action": "meet",
            "location": friend["location"],
            "person": friend["name"],
            "start_time": minutes_to_time(meeting_start),
            "end_time": minutes_to_time(meeting_end)
        })
        
        current_location = friend["location"]
        current_time = meeting_end
    
    return schedule

def evaluate_schedule(schedule):
    if not schedule:
        return -1
    return len(schedule)

# Try different orders to maximize number of friends met
best_schedule = []
best_score = 0

# We'll prioritize friends with tighter time windows first
friend_names = [f["name"] for f in friends]
# Try all possible permutations is too expensive, so we'll try a reasonable subset
for perm in permutations(friend_names, min(5, len(friend_names))):
    schedule = calculate_schedule(perm)
    score = evaluate_schedule(schedule)
    if score > best_score:
        best_score = score
        best_schedule = schedule

# If no schedule meets all, try to find one that meets most
if best_score < len(friends):
    for friend in friends:
        single_schedule = calculate_schedule([friend["name"]])
        if single_schedule and evaluate_schedule(single_schedule) > best_score:
            best_score = evaluate_schedule(single_schedule)
            best_schedule = single_schedule

# After some attempts, build a reasonable schedule manually if needed
if not best_schedule:
    # Build a schedule that meets the most critical friends
    manual_order = ["Kimberly", "William", "Joshua", "Mary", "Patricia", "George", "Charles", "Ronald", "Kenneth", "David"]
    best_schedule = calculate_schedule(manual_order)
    if not best_schedule:
        manual_order = ["Kimberly", "William", "Joshua", "Mary", "Patricia"]
        best_schedule = calculate_schedule(manual_order)

# Prepare output
output = {
    "itinerary": best_schedule if best_schedule else []
}

print(json.dumps(output, indent=2))