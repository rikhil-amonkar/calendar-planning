import json
from itertools import permutations

def time_to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Define travel times as a dictionary of dictionaries
travel_times = {
    "Embarcadero": {
        "Bayview": 21, "Chinatown": 7, "Alamo Square": 19, "Nob Hill": 10,
        "Presidio": 20, "Union Square": 10, "The Castro": 25, "North Beach": 5,
        "Fisherman's Wharf": 6, "Marina District": 12
    },
    "Bayview": {
        "Embarcadero": 19, "Chinatown": 19, "Alamo Square": 16, "Nob Hill": 20,
        "Presidio": 32, "Union Square": 18, "The Castro": 19, "North Beach": 22,
        "Fisherman's Wharf": 25, "Marina District": 27
    },
    "Chinatown": {
        "Embarcadero": 5, "Bayview": 20, "Alamo Square": 17, "Nob Hill": 9,
        "Presidio": 19, "Union Square": 7, "The Castro": 22, "North Beach": 3,
        "Fisherman's Wharf": 8, "Marina District": 12
    },
    "Alamo Square": {
        "Embarcadero": 16, "Bayview": 16, "Chinatown": 15, "Nob Hill": 11,
        "Presidio": 17, "Union Square": 14, "The Castro": 8, "North Beach": 15,
        "Fisherman's Wharf": 19, "Marina District": 15
    },
    "Nob Hill": {
        "Embarcadero": 9, "Bayview": 19, "Chinatown": 6, "Alamo Square": 11,
        "Presidio": 17, "Union Square": 7, "The Castro": 17, "North Beach": 8,
        "Fisherman's Wharf": 10, "Marina District": 11
    },
    "Presidio": {
        "Embarcadero": 20, "Bayview": 31, "Chinatown": 21, "Alamo Square": 19,
        "Nob Hill": 18, "Union Square": 22, "The Castro": 21, "North Beach": 18,
        "Fisherman's Wharf": 19, "Marina District": 11
    },
    "Union Square": {
        "Embarcadero": 11, "Bayview": 15, "Chinatown": 7, "Alamo Square": 15,
        "Nob Hill": 9, "Presidio": 24, "The Castro": 17, "North Beach": 10,
        "Fisherman's Wharf": 15, "Marina District": 18
    },
    "The Castro": {
        "Embarcadero": 22, "Bayview": 19, "Chinatown": 22, "Alamo Square": 8,
        "Nob Hill": 16, "Presidio": 20, "Union Square": 19, "North Beach": 20,
        "Fisherman's Wharf": 24, "Marina District": 21
    },
    "North Beach": {
        "Embarcadero": 6, "Bayview": 25, "Chinatown": 6, "Alamo Square": 16,
        "Nob Hill": 7, "Presidio": 17, "Union Square": 7, "The Castro": 23,
        "Fisherman's Wharf": 5, "Marina District": 9
    },
    "Fisherman's Wharf": {
        "Embarcadero": 8, "Bayview": 26, "Chinatown": 12, "Alamo Square": 21,
        "Nob Hill": 11, "Presidio": 17, "Union Square": 13, "The Castro": 27,
        "North Beach": 6, "Marina District": 9
    },
    "Marina District": {
        "Embarcadero": 14, "Bayview": 27, "Chinatown": 15, "Alamo Square": 15,
        "Nob Hill": 12, "Presidio": 10, "Union Square": 16, "The Castro": 22,
        "North Beach": 11, "Fisherman's Wharf": 10
    }
}

# Define friends' availability and constraints
friends = [
    {"name": "Matthew", "location": "Bayview", "start": "19:15", "end": "22:00", "min_duration": 120},
    {"name": "Karen", "location": "Chinatown", "start": "19:15", "end": "21:15", "min_duration": 90},
    {"name": "Sarah", "location": "Alamo Square", "start": "20:00", "end": "21:45", "min_duration": 105},
    {"name": "Jessica", "location": "Nob Hill", "start": "16:30", "end": "18:45", "min_duration": 120},
    {"name": "Stephanie", "location": "Presidio", "start": "7:30", "end": "10:15", "min_duration": 60},
    {"name": "Mary", "location": "Union Square", "start": "16:45", "end": "21:30", "min_duration": 60},
    {"name": "Charles", "location": "The Castro", "start": "16:30", "end": "22:00", "min_duration": 105},
    {"name": "Nancy", "location": "North Beach", "start": "14:45", "end": "20:00", "min_duration": 15},
    {"name": "Thomas", "location": "Fisherman's Wharf", "start": "13:30", "end": "19:00", "min_duration": 30},
    {"name": "Brian", "location": "Marina District", "start": "12:15", "end": "18:00", "min_duration": 60}
]

current_location = "Embarcadero"
current_time = time_to_minutes("9:00")
itinerary = []

# Helper function to check if a meeting is possible
def can_meet(friend, arrival_time):
    start = time_to_minutes(friend["start"])
    end = time_to_minutes(friend["end"])
    min_duration = friend["min_duration"]
    
    if arrival_time > end:
        return False
    
    meeting_start = max(arrival_time, start)
    meeting_end = min(meeting_start + min_duration, end)
    
    if meeting_end - meeting_start >= min_duration:
        return (meeting_start, meeting_end)
    return False

# Try to meet as many friends as possible in order of priority
# Priority is based on who has the earliest end time
friends_sorted = sorted(friends, key=lambda x: time_to_minutes(x["end"]))

for friend in friends_sorted:
    travel_time = travel_times[current_location][friend["location"]]
    arrival_time = current_time + travel_time
    meeting = can_meet(friend, arrival_time)
    
    if meeting:
        meeting_start, meeting_end = meeting
        itinerary.append({
            "action": "meet",
            "location": friend["location"],
            "person": friend["name"],
            "start_time": minutes_to_time(meeting_start),
            "end_time": minutes_to_time(meeting_end)
        })
        current_time = meeting_end
        current_location = friend["location"]

# Output the itinerary
output = {"itinerary": itinerary}
print(json.dumps(output, indent=2))