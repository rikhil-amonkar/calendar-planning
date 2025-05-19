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
friends = {
    "Emily": {
        "location": "Richmond District",
        "available_start": "19:00",
        "available_end": "21:00",
        "min_duration": 15
    },
    "Margaret": {
        "location": "Financial District",
        "available_start": "16:30",
        "available_end": "20:15",
        "min_duration": 75
    },
    "Ronald": {
        "location": "North Beach",
        "available_start": "18:30",
        "available_end": "19:30",
        "min_duration": 45
    },
    "Deborah": {
        "location": "The Castro",
        "available_start": "13:45",
        "available_end": "21:15",
        "min_duration": 90
    },
    "Jeffrey": {
        "location": "Golden Gate Park",
        "available_start": "11:15",
        "available_end": "14:30",
        "min_duration": 120
    }
}

travel_times = {
    "Nob Hill": {
        "Richmond District": 14,
        "Financial District": 9,
        "North Beach": 8,
        "The Castro": 17,
        "Golden Gate Park": 17
    },
    "Richmond District": {
        "Nob Hill": 17,
        "Financial District": 22,
        "North Beach": 17,
        "The Castro": 16,
        "Golden Gate Park": 9
    },
    "Financial District": {
        "Nob Hill": 8,
        "Richmond District": 21,
        "North Beach": 7,
        "The Castro": 23,
        "Golden Gate Park": 23
    },
    "North Beach": {
        "Nob Hill": 7,
        "Richmond District": 18,
        "Financial District": 8,
        "The Castro": 22,
        "Golden Gate Park": 22
    },
    "The Castro": {
        "Nob Hill": 16,
        "Richmond District": 16,
        "Financial District": 20,
        "North Beach": 20,
        "Golden Gate Park": 11
    },
    "Golden Gate Park": {
        "Nob Hill": 20,
        "Richmond District": 7,
        "Financial District": 26,
        "North Beach": 24,
        "The Castro": 13
    }
}

current_location = "Nob Hill"
current_time = time_to_minutes("9:00")
itinerary = []

def can_schedule_meeting(friend_order):
    temp_itinerary = []
    temp_location = current_location
    temp_time = current_time
    
    for friend in friend_order:
        data = friends[friend]
        location = data["location"]
        travel_time = travel_times[temp_location].get(location, float('inf'))
        
        # Arrive at location
        arrival_time = temp_time + travel_time
        available_start = time_to_minutes(data["available_start"])
        available_end = time_to_minutes(data["available_end"])
        min_duration = data["min_duration"]
        
        # Calculate meeting window
        start_time = max(arrival_time, available_start)
        end_time = min(start_time + min_duration, available_end)
        
        if end_time - start_time < min_duration:
            return None
        
        temp_itinerary.append({
            "action": "meet",
            "location": location,
            "person": friend,
            "start_time": minutes_to_time(start_time),
            "end_time": minutes_to_time(end_time)
        })
        
        temp_location = location
        temp_time = end_time
    
    return temp_itinerary

# Try all possible orders to find the best schedule
best_itinerary = None
max_meetings = 0

for perm in permutations(friends.keys()):
    itinerary = can_schedule_meeting(perm)
    if itinerary and len(itinerary) > max_meetings:
        best_itinerary = itinerary
        max_meetings = len(itinerary)
    elif itinerary and len(itinerary) == max_meetings and best_itinerary:
        # Prefer longer total meeting time
        current_duration = sum(time_to_minutes(m["end_time"]) - time_to_minutes(m["start_time"]) for m in itinerary)
        best_duration = sum(time_to_minutes(m["end_time"]) - time_to_minutes(m["start_time"]) for m in best_itinerary)
        if current_duration > best_duration:
            best_itinerary = itinerary

if not best_itinerary:
    # Try to find partial schedules if full schedule isn't possible
    for num_meetings in range(len(friends)-1, 0, -1):
        for perm in permutations(friends.keys(), num_meetings):
            itinerary = can_schedule_meeting(perm)
            if itinerary:
                best_itinerary = itinerary
                break
        if best_itinerary:
            break

output = {"itinerary": best_itinerary} if best_itinerary else {"itinerary": []}
print(json.dumps(output, indent=2))