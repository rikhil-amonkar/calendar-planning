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
travel_times = {
    "Mission District": {
        "The Castro": 7,
        "Nob Hill": 12,
        "Presidio": 25,
        "Marina District": 19,
        "Pacific Heights": 16,
        "Golden Gate Park": 17,
        "Chinatown": 16,
        "Richmond District": 20
    },
    "The Castro": {
        "Mission District": 7,
        "Nob Hill": 16,
        "Presidio": 20,
        "Marina District": 21,
        "Pacific Heights": 16,
        "Golden Gate Park": 11,
        "Chinatown": 22,
        "Richmond District": 16
    },
    "Nob Hill": {
        "Mission District": 13,
        "The Castro": 17,
        "Presidio": 17,
        "Marina District": 11,
        "Pacific Heights": 8,
        "Golden Gate Park": 17,
        "Chinatown": 6,
        "Richmond District": 14
    },
    "Presidio": {
        "Mission District": 26,
        "The Castro": 21,
        "Nob Hill": 18,
        "Marina District": 11,
        "Pacific Heights": 11,
        "Golden Gate Park": 12,
        "Chinatown": 21,
        "Richmond District": 7
    },
    "Marina District": {
        "Mission District": 20,
        "The Castro": 22,
        "Nob Hill": 12,
        "Presidio": 10,
        "Pacific Heights": 7,
        "Golden Gate Park": 18,
        "Chinatown": 15,
        "Richmond District": 11
    },
    "Pacific Heights": {
        "Mission District": 15,
        "The Castro": 16,
        "Nob Hill": 8,
        "Presidio": 11,
        "Marina District": 6,
        "Golden Gate Park": 15,
        "Chinatown": 11,
        "Richmond District": 12
    },
    "Golden Gate Park": {
        "Mission District": 17,
        "The Castro": 13,
        "Nob Hill": 20,
        "Presidio": 11,
        "Marina District": 16,
        "Pacific Heights": 16,
        "Chinatown": 23,
        "Richmond District": 7
    },
    "Chinatown": {
        "Mission District": 17,
        "The Castro": 22,
        "Nob Hill": 9,
        "Presidio": 19,
        "Marina District": 12,
        "Pacific Heights": 10,
        "Golden Gate Park": 23,
        "Richmond District": 20
    },
    "Richmond District": {
        "Mission District": 20,
        "The Castro": 16,
        "Nob Hill": 17,
        "Presidio": 7,
        "Marina District": 9,
        "Pacific Heights": 10,
        "Golden Gate Park": 9,
        "Chinatown": 20
    }
}

friends = [
    {"name": "Lisa", "location": "The Castro", "start": "19:15", "end": "21:15", "duration": 120},
    {"name": "Daniel", "location": "Nob Hill", "start": "8:15", "end": "11:00", "duration": 15},
    {"name": "Elizabeth", "location": "Presidio", "start": "21:15", "end": "22:15", "duration": 45},
    {"name": "Steven", "location": "Marina District", "start": "16:30", "end": "20:45", "duration": 90},
    {"name": "Timothy", "location": "Pacific Heights", "start": "12:00", "end": "18:00", "duration": 90},
    {"name": "Ashley", "location": "Golden Gate Park", "start": "20:45", "end": "21:45", "duration": 60},
    {"name": "Kevin", "location": "Chinatown", "start": "12:00", "end": "19:00", "duration": 30},
    {"name": "Betty", "location": "Richmond District", "start": "13:15", "end": "15:45", "duration": 30}
]

current_location = "Mission District"
current_time = time_to_minutes("9:00")

def get_possible_meetings(current_time, current_location, friends_met):
    possible = []
    for friend in friends:
        if friend["name"] in friends_met:
            continue
        start = time_to_minutes(friend["start"])
        end = time_to_minutes(friend["end"])
        travel_time = travel_times[current_location][friend["location"]]
        arrival_time = current_time + travel_time
        if arrival_time > end:
            continue
        meeting_end = min(arrival_time + friend["duration"], end)
        possible.append((friend, arrival_time, meeting_end))
    return possible

def schedule_meetings(current_time, current_location, friends_met, itinerary):
    possible = get_possible_meetings(current_time, current_location, friends_met)
    if not possible:
        return itinerary
    
    best_itinerary = itinerary
    best_count = len(friends_met)
    
    for meeting in possible:
        friend, start, end = meeting
        new_friends_met = friends_met.copy()
        new_friends_met.add(friend["name"])
        new_itinerary = itinerary.copy()
        new_itinerary.append({
            "action": "meet",
            "location": friend["location"],
            "person": friend["name"],
            "start_time": minutes_to_time(start),
            "end_time": minutes_to_time(end)
        })
        result_itinerary = schedule_meetings(end, friend["location"], new_friends_met, new_itinerary)
        if len(new_friends_met) > best_count:
            best_count = len(new_friends_met)
            best_itinerary = result_itinerary
    
    return best_itinerary

initial_itinerary = []
initial_friends_met = set()
optimal_itinerary = schedule_meetings(current_time, current_location, initial_friends_met, initial_itinerary)

output = {"itinerary": optimal_itinerary}
print(json.dumps(output, indent=2))