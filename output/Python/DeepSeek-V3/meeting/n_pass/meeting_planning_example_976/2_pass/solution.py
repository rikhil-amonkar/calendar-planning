import json
from itertools import permutations

def time_to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

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

def generate_itinerary(friends_to_meet, current_loc, current_time):
    itinerary = []
    for friend in friends_to_meet:
        travel_time = travel_times[current_loc][friend["location"]]
        arrival_time = current_time + travel_time
        start_window = time_to_minutes(friend["start"])
        end_window = time_to_minutes(friend["end"])
        min_duration = friend["min_duration"]
        
        # Calculate possible meeting time
        meeting_start = max(arrival_time, start_window)
        meeting_end = meeting_start + min_duration
        
        if meeting_end > end_window:
            return None  # Can't meet this friend
        
        itinerary.append({
            "action": "meet",
            "location": friend["location"],
            "person": friend["name"],
            "start_time": minutes_to_time(meeting_start),
            "end_time": minutes_to_time(meeting_end)
        })
        current_time = meeting_end
        current_loc = friend["location"]
    return itinerary

# Try different orders to maximize number of meetings
best_itinerary = []
current_location = "Embarcadero"
current_time = time_to_minutes("9:00")

# We'll try different subsets and orders of friends to find the best itinerary
for size in range(len(friends), 0, -1):
    for subset in permutations(friends, size):
        itinerary = generate_itinerary(subset, current_location, current_time)
        if itinerary and len(itinerary) > len(best_itinerary):
            best_itinerary = itinerary
            if len(best_itinerary) == len(friends):  # Found maximum possible
                break
    if best_itinerary:
        break

# Output the best itinerary found
output = {"itinerary": best_itinerary}
print(json.dumps(output, indent=2))