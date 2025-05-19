import json
from itertools import permutations

# Travel times dictionary
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

# Friend data
friends = [
    {"name": "Charles", "location": "Presidio", "start": 13.25, "end": 15.0, "duration": 1.75},
    {"name": "Robert", "location": "Nob Hill", "start": 13.25, "end": 17.5, "duration": 1.5},
    {"name": "Nancy", "location": "Pacific Heights", "start": 14.75, "end": 22.0, "duration": 1.75},
    {"name": "Brian", "location": "Mission District", "start": 15.5, "end": 22.0, "duration": 1.0},
    {"name": "Kimberly", "location": "Marina District", "start": 17.0, "end": 19.75, "duration": 1.25},
    {"name": "David", "location": "North Beach", "start": 14.75, "end": 16.5, "duration": 1.25},
    {"name": "William", "location": "Russian Hill", "start": 12.5, "end": 19.25, "duration": 2.0},
    {"name": "Jeffrey", "location": "Richmond District", "start": 12.0, "end": 19.25, "duration": 0.75},
    {"name": "Karen", "location": "Embarcadero", "start": 14.25, "end": 20.75, "duration": 1.0},
    {"name": "Joshua", "location": "Alamo Square", "start": 18.75, "end": 22.0, "duration": 1.0}
]

def time_to_float(time_str):
    hours, minutes = map(int, time_str.split(':'))
    return hours + minutes / 60.0

def float_to_time(time_float):
    hours = int(time_float)
    minutes = int((time_float - hours) * 60)
    return f"{hours}:{minutes:02d}"

def calculate_schedule(order):
    current_location = "Sunset District"
    current_time = 9.0
    itinerary = []
    met_friends = set()
    
    for friend_name in order:
        friend = next(f for f in friends if f["name"] == friend_name)
        
        # Travel to friend's location
        travel_time = travel_times[current_location][friend["location"]] / 60.0
        arrival_time = current_time + travel_time
        
        # Check if we can meet this friend
        meeting_start = max(arrival_time, friend["start"])
        meeting_end = meeting_start + friend["duration"]
        
        if meeting_end > friend["end"]:
            return None  # Can't meet this friend
        
        # Add to itinerary
        itinerary.append({
            "action": "meet",
            "location": friend["location"],
            "person": friend["name"],
            "start_time": float_to_time(meeting_start),
            "end_time": float_to_time(meeting_end)
        })
        
        met_friends.add(friend["name"])
        current_location = friend["location"]
        current_time = meeting_end
    
    return itinerary if len(met_friends) == len(friends) else None

def find_optimal_schedule():
    friend_names = [f["name"] for f in friends]
    
    # Try all possible orders (permutations) of meeting friends
    for perm in permutations(friend_names):
        schedule = calculate_schedule(perm)
        if schedule:
            return schedule
    
    # If no complete schedule found, try to maximize number of meetings
    max_meetings = 0
    best_schedule = None
    
    for perm in permutations(friend_names):
        schedule = calculate_schedule(perm)
        if schedule and len(schedule) > max_meetings:
            max_meetings = len(schedule)
            best_schedule = schedule
    
    return best_schedule

optimal_schedule = find_optimal_schedule()

if optimal_schedule:
    result = {"itinerary": optimal_schedule}
else:
    result = {"itinerary": []}

print(json.dumps(result, indent=2))