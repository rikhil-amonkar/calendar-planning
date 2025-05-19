import json
from itertools import permutations

def time_to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Input data
friends = {
    "Linda": {"location": "Marina District", "start": "18:00", "end": "22:00", "duration": 30},
    "Kenneth": {"location": "The Castro", "start": "14:45", "end": "16:15", "duration": 30},
    "Kimberly": {"location": "Richmond District", "start": "14:15", "end": "22:00", "duration": 30},
    "Paul": {"location": "Alamo Square", "start": "21:00", "end": "21:30", "duration": 15},
    "Carol": {"location": "Financial District", "start": "10:15", "end": "12:00", "duration": 60},
    "Brian": {"location": "Presidio", "start": "10:00", "end": "21:30", "duration": 75},
    "Laura": {"location": "Mission District", "start": "16:15", "end": "20:30", "duration": 30},
    "Sandra": {"location": "Nob Hill", "start": "9:15", "end": "18:30", "duration": 60},
    "Karen": {"location": "Russian Hill", "start": "18:30", "end": "22:00", "duration": 75}
}

travel_times = {
    "Pacific Heights": {
        "Marina District": 6, "The Castro": 16, "Richmond District": 12, "Alamo Square": 10,
        "Financial District": 13, "Presidio": 11, "Mission District": 15, "Nob Hill": 8, "Russian Hill": 7
    },
    "Marina District": {
        "Pacific Heights": 7, "The Castro": 22, "Richmond District": 11, "Alamo Square": 15,
        "Financial District": 17, "Presidio": 10, "Mission District": 20, "Nob Hill": 12, "Russian Hill": 8
    },
    "The Castro": {
        "Pacific Heights": 16, "Marina District": 21, "Richmond District": 16, "Alamo Square": 8,
        "Financial District": 21, "Presidio": 20, "Mission District": 7, "Nob Hill": 16, "Russian Hill": 18
    },
    "Richmond District": {
        "Pacific Heights": 10, "Marina District": 9, "The Castro": 16, "Alamo Square": 13,
        "Financial District": 22, "Presidio": 7, "Mission District": 20, "Nob Hill": 17, "Russian Hill": 13
    },
    "Alamo Square": {
        "Pacific Heights": 10, "Marina District": 15, "The Castro": 8, "Richmond District": 11,
        "Financial District": 17, "Presidio": 17, "Mission District": 10, "Nob Hill": 11, "Russian Hill": 13
    },
    "Financial District": {
        "Pacific Heights": 13, "Marina District": 15, "The Castro": 20, "Richmond District": 21,
        "Alamo Square": 17, "Presidio": 22, "Mission District": 17, "Nob Hill": 8, "Russian Hill": 11
    },
    "Presidio": {
        "Pacific Heights": 11, "Marina District": 11, "The Castro": 21, "Richmond District": 7,
        "Alamo Square": 19, "Financial District": 23, "Mission District": 26, "Nob Hill": 18, "Russian Hill": 14
    },
    "Mission District": {
        "Pacific Heights": 16, "Marina District": 19, "The Castro": 7, "Richmond District": 20,
        "Alamo Square": 11, "Financial District": 15, "Presidio": 25, "Nob Hill": 12, "Russian Hill": 15
    },
    "Nob Hill": {
        "Pacific Heights": 8, "Marina District": 11, "The Castro": 17, "Richmond District": 14,
        "Alamo Square": 11, "Financial District": 9, "Presidio": 17, "Mission District": 13, "Russian Hill": 5
    },
    "Russian Hill": {
        "Pacific Heights": 7, "Marina District": 7, "The Castro": 21, "Richmond District": 14,
        "Alamo Square": 15, "Financial District": 11, "Presidio": 14, "Mission District": 16, "Nob Hill": 5
    }
}

current_location = "Pacific Heights"
current_time = time_to_minutes("9:00")
itinerary = []

# Helper function to get travel time
def get_travel_time(from_loc, to_loc):
    if from_loc == to_loc:
        return 0
    try:
        return travel_times[from_loc][to_loc]
    except KeyError:
        return travel_times[to_loc][from_loc]

# Function to check if a meeting is possible
def can_meet(person, start_time, end_time):
    friend = friends[person]
    friend_start = time_to_minutes(friend["start"])
    friend_end = time_to_minutes(friend["end"])
    duration = friend["duration"]
    
    # Check if meeting fits in friend's availability
    meeting_start = max(start_time, friend_start)
    meeting_end = min(end_time, friend_end)
    
    if meeting_end - meeting_start >= duration:
        return True, meeting_start, meeting_start + duration
    return False, 0, 0

# Prioritize friends with tighter time windows first
priority_order = ["Paul", "Carol", "Kenneth", "Laura", "Linda", "Karen", "Brian", "Kimberly", "Sandra"]

scheduled = set()

for person in priority_order:
    if person in scheduled:
        continue
        
    friend = friends[person]
    location = friend["location"]
    travel_time = get_travel_time(current_location, location)
    
    # Calculate possible meeting times
    possible_start = current_time + travel_time
    possible_end = time_to_minutes(friend["end"])
    
    can_meet_flag, meeting_start, meeting_end = can_meet(person, possible_start, possible_end)
    
    if can_meet_flag:
        # Schedule the meeting
        itinerary.append({
            "action": "meet",
            "location": location,
            "person": person,
            "start_time": minutes_to_time(meeting_start),
            "end_time": minutes_to_time(meeting_end)
        })
        scheduled.add(person)
        current_location = location
        current_time = meeting_end

# Output the itinerary
output = {
    "itinerary": itinerary
}

print(json.dumps(output, indent=2))