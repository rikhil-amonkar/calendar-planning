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
travel_times = {
    ('Sunset District', 'Chinatown'): 30,
    ('Sunset District', 'Russian Hill'): 24,
    ('Sunset District', 'North Beach'): 29,
    ('Chinatown', 'Sunset District'): 29,
    ('Chinatown', 'Russian Hill'): 7,
    ('Chinatown', 'North Beach'): 3,
    ('Russian Hill', 'Sunset District'): 23,
    ('Russian Hill', 'Chinatown'): 9,
    ('Russian Hill', 'North Beach'): 5,
    ('North Beach', 'Sunset District'): 27,
    ('North Beach', 'Chinatown'): 6,
    ('North Beach', 'Russian Hill'): 4
}

# Constraints
current_location = "Sunset District"
current_time = time_to_minutes("9:00")

friends = [
    {"name": "Anthony", "location": "Chinatown", "available_start": time_to_minutes("13:15"), "available_end": time_to_minutes("14:30"), "min_duration": 60},
    {"name": "Rebecca", "location": "Russian Hill", "available_start": time_to_minutes("19:30"), "available_end": time_to_minutes("21:15"), "min_duration": 105},
    {"name": "Melissa", "location": "North Beach", "available_start": time_to_minutes("8:15"), "available_end": time_to_minutes("13:30"), "min_duration": 105}
]

# Generate all possible orders to meet friends
best_itinerary = []
max_meetings = 0

for order in permutations(friends):
    itinerary = []
    temp_location = current_location
    temp_time = current_time
    possible = True
    
    for friend in order:
        # Calculate travel time
        travel_time = travel_times.get((temp_location, friend["location"]), float('inf'))
        arrival_time = temp_time + travel_time
        
        # Check if we can meet the friend
        meeting_start = max(arrival_time, friend["available_start"])
        meeting_end = meeting_start + friend["min_duration"]
        
        if meeting_end > friend["available_end"]:
            possible = False
            break
        
        itinerary.append({
            "action": "meet",
            "location": friend["location"],
            "person": friend["name"],
            "start_time": minutes_to_time(meeting_start),
            "end_time": minutes_to_time(meeting_end)
        })
        
        temp_location = friend["location"]
        temp_time = meeting_end
    
    if possible and len(itinerary) > max_meetings:
        max_meetings = len(itinerary)
        best_itinerary = itinerary
    elif possible and len(itinerary) == max_meetings:
        # Prefer longer total meeting time or other criteria if needed
        best_itinerary = itinerary

# Output the result
output = {"itinerary": best_itinerary}
print(json.dumps(output, indent=2))