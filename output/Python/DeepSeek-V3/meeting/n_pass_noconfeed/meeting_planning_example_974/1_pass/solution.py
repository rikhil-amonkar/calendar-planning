import json
from itertools import permutations

def time_to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Initialize travel times as a dictionary of dictionaries
travel_times = {
    "Sunset District": {
        "Presidio": 16, "Nob Hill": 27, "Pacific Heights": 21, "Mission District": 25,
        "Marina District": 21, "North Beach": 28, "Russian Hill": 24, "Richmond District": 12,
        "Embarcadero": 30, "Alamo Square": 17
    },
    "Presidio": {
        "Sunset District": 15, "Nob Hill": 18, "Pacific Heights": 11, "Mission District": 26,
        "Marina District": 11, "North Beach": 18, "Russian Hill": 14, "Richmond District": 7,
        "Embarcadero": 20, "Alamo Square": 19
    },
    "Nob Hill": {
        "Sunset District": 24, "Presidio": 17, "Pacific Heights": 8, "Mission District": 13,
        "Marina District": 11, "North Beach": 8, "Russian Hill": 5, "Richmond District": 14,
        "Embarcadero": 9, "Alamo Square": 11
    },
    "Pacific Heights": {
        "Sunset District": 21, "Presidio": 11, "Nob Hill": 8, "Mission District": 15,
        "Marina District": 6, "North Beach": 9, "Russian Hill": 7, "Richmond District": 12,
        "Embarcadero": 10, "Alamo Square": 10
    },
    "Mission District": {
        "Sunset District": 24, "Presidio": 25, "Nob Hill": 12, "Pacific Heights": 16,
        "Marina District": 19, "North Beach": 17, "Russian Hill": 15, "Richmond District": 20,
        "Embarcadero": 19, "Alamo Square": 11
    },
    "Marina District": {
        "Sunset District": 19, "Presidio": 10, "Nob Hill": 12, "Pacific Heights": 7,
        "Mission District": 20, "North Beach": 11, "Russian Hill": 8, "Richmond District": 11,
        "Embarcadero": 14, "Alamo Square": 15
    },
    "North Beach": {
        "Sunset District": 27, "Presidio": 17, "Nob Hill": 7, "Pacific Heights": 8,
        "Mission District": 18, "Marina District": 9, "Russian Hill": 4, "Richmond District": 18,
        "Embarcadero": 6, "Alamo Square": 16
    },
    "Russian Hill": {
        "Sunset District": 23, "Presidio": 14, "Nob Hill": 5, "Pacific Heights": 7,
        "Mission District": 16, "Marina District": 7, "North Beach": 5, "Richmond District": 14,
        "Embarcadero": 8, "Alamo Square": 15
    },
    "Richmond District": {
        "Sunset District": 11, "Presidio": 7, "Nob Hill": 17, "Pacific Heights": 10,
        "Mission District": 20, "Marina District": 9, "North Beach": 17, "Russian Hill": 13,
        "Embarcadero": 19, "Alamo Square": 13
    },
    "Embarcadero": {
        "Sunset District": 30, "Presidio": 20, "Nob Hill": 10, "Pacific Heights": 11,
        "Mission District": 20, "Marina District": 12, "North Beach": 5, "Russian Hill": 8,
        "Richmond District": 21, "Alamo Square": 19
    },
    "Alamo Square": {
        "Sunset District": 16, "Presidio": 17, "Nob Hill": 11, "Pacific Heights": 10,
        "Mission District": 10, "Marina District": 15, "North Beach": 15, "Russian Hill": 13,
        "Richmond District": 11, "Embarcadero": 16
    }
}

# Define friends and their constraints
friends = [
    {"name": "Charles", "location": "Presidio", "start": "13:15", "end": "15:00", "duration": 105},
    {"name": "Robert", "location": "Nob Hill", "start": "13:15", "end": "17:30", "duration": 90},
    {"name": "Nancy", "location": "Pacific Heights", "start": "14:45", "end": "22:00", "duration": 105},
    {"name": "Brian", "location": "Mission District", "start": "15:30", "end": "22:00", "duration": 60},
    {"name": "Kimberly", "location": "Marina District", "start": "17:00", "end": "19:45", "duration": 75},
    {"name": "David", "location": "North Beach", "start": "14:45", "end": "16:30", "duration": 75},
    {"name": "William", "location": "Russian Hill", "start": "12:30", "end": "19:15", "duration": 120},
    {"name": "Jeffrey", "location": "Richmond District", "start": "12:00", "end": "19:15", "duration": 45},
    {"name": "Karen", "location": "Embarcadero", "start": "14:15", "end": "20:45", "duration": 60},
    {"name": "Joshua", "location": "Alamo Square", "start": "18:45", "end": "22:00", "duration": 60}
]

# Filter friends to only those we can meet given their constraints
possible_friends = [f for f in friends if time_to_minutes(f["end"]) - time_to_minutes(f["start"]) >= f["duration"]]

# We'll try to meet as many friends as possible, prioritizing those with tighter time windows
# Start at Sunset District at 9:00
current_location = "Sunset District"
current_time = time_to_minutes("9:00")
itinerary = []

# Sort friends by end time (earlier first) to prioritize those with tighter windows
possible_friends.sort(key=lambda x: time_to_minutes(x["end"]))

for friend in possible_friends:
    travel_time = travel_times[current_location][friend["location"]]
    arrival_time = current_time + travel_time
    start_time = max(arrival_time, time_to_minutes(friend["start"]))
    end_time = start_time + friend["duration"]
    
    if end_time <= time_to_minutes(friend["end"]):
        itinerary.append({
            "action": "meet",
            "location": friend["location"],
            "person": friend["name"],
            "start_time": minutes_to_time(start_time),
            "end_time": minutes_to_time(end_time)
        })
        current_time = end_time
        current_location = friend["location"]

# Convert itinerary to JSON
output = {"itinerary": itinerary}
print(json.dumps(output, indent=2))