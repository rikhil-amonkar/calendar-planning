import itertools
import json

def time_to_minutes(t_str):
    period = t_str[-2:]
    time_part = t_str[:-2].strip()
    parts = time_part.split(':')
    hour = int(parts[0])
    minute = int(parts[1]) if len(parts) > 1 else 0
    if period == 'PM' and hour != 12:
        hour += 12
    elif period == 'AM' and hour == 12:
        hour = 0
    return hour * 60 + minute

def minutes_to_time(minutes):
    hour = minutes // 60
    minute = minutes % 60
    return f"{hour}:{minute:02d}"

travel_times = {
    "Mission District": {
        "Alamo Square": 11, "Presidio": 25, "Russian Hill": 15, "North Beach": 17,
        "Golden Gate Park": 17, "Richmond District": 20, "Embarcadero": 19,
        "Financial District": 15, "Marina District": 19
    },
    "Alamo Square": {
        "Mission District": 10, "Presidio": 17, "Russian Hill": 13, "North Beach": 15,
        "Golden Gate Park": 9, "Richmond District": 11, "Embarcadero": 16,
        "Financial District": 17, "Marina District": 15
    },
    "Presidio": {
        "Mission District": 26, "Alamo Square": 19, "Russian Hill": 14, "North Beach": 18,
        "Golden Gate Park": 12, "Richmond District": 7, "Embarcadero": 20,
        "Financial District": 23, "Marina District": 11
    },
    "Russian Hill": {
        "Mission District": 16, "Alamo Square": 15, "Presidio": 14, "North Beach": 5,
        "Golden Gate Park": 21, "Richmond District": 14, "Embarcadero": 8,
        "Financial District": 11, "Marina District": 7
    },
    "North Beach": {
        "Mission District": 18, "Alamo Square": 16, "Presidio": 17, "Russian Hill": 4,
        "Golden Gate Park": 22, "Richmond District": 18, "Embarcadero": 6,
        "Financial District": 8, "Marina District": 9
    },
    "Golden Gate Park": {
        "Mission District": 17, "Alamo Square": 9, "Presidio": 11, "Russian Hill": 19,
        "North Beach": 23, "Richmond District": 7, "Embarcadero": 25,
        "Financial District": 26, "Marina District": 16
    },
    "Richmond District": {
        "Mission District": 20, "Alamo Square": 13, "Presidio": 7, "Russian Hill": 13,
        "North Beach": 17, "Golden Gate Park": 9, "Embarcadero": 19,
        "Financial District": 22, "Marina District": 9
    },
    "Embarcadero": {
        "Mission District": 20, "Alamo Square": 19, "Presidio": 20, "Russian Hill": 8,
        "North Beach": 5, "Golden Gate Park": 25, "Richmond District": 21,
        "Financial District": 5, "Marina District": 12
    },
    "Financial District": {
        "Mission District": 17, "Alamo Square": 17, "Presidio": 22, "Russian Hill": 11,
        "North Beach": 7, "Golden Gate Park": 23, "Richmond District": 21,
        "Embarcadero": 4, "Marina District": 15
    },
    "Marina District": {
        "Mission District": 20, "Alamo Square": 15, "Presidio": 10, "Russian Hill": 8,
        "North Beach": 11, "Golden Gate Park": 18, "Richmond District": 11,
        "Embarcadero": 14, "Financial District": 17
    }
}

friends = [
    {"name": "Laura", "location": "Alamo Square", "start": time_to_minutes("2:30PM"), "end": time_to_minutes("4:15PM"), "duration": 75},
    {"name": "Brian", "location": "Presidio", "start": time_to_minutes("10:15AM"), "end": time_to_minutes("5:00PM"), "duration": 30},
    {"name": "Karen", "location": "Russian Hill", "start": time_to_minutes("6:00PM"), "end": time_to_minutes("8:15PM"), "duration": 90},
    {"name": "Stephanie", "location": "North Beach", "start": time_to_minutes("10:15AM"), "end": time_to_minutes("4:00PM"), "duration": 75},
    {"name": "Helen", "location": "Golden Gate Park", "start": time_to_minutes("11:30AM"), "end": time_to_minutes("9:45PM"), "duration": 120},
    {"name": "Sandra", "location": "Richmond District", "start": time_to_minutes("8:00AM"), "end": time_to_minutes("3:15PM"), "duration": 30},
    {"name": "Mary", "location": "Embarcadero", "start": time_to_minutes("4:45PM"), "end": time_to_minutes("6:45PM"), "duration": 120},
    {"name": "Deborah", "location": "Financial District", "start": time_to_minutes("7:00PM"), "end": time_to_minutes("8:45PM"), "duration": 105},
    {"name": "Elizabeth", "location": "Marina District", "start": time_to_minutes("8:30AM"), "end": time_to_minutes("1:15PM"), "duration": 105}
]

start_time = 540  # 9:00AM in minutes
start_location = "Mission District"
best_count = 0
best_itinerary = []

permutations = list(itertools.permutations(friends))
for perm in permutations:
    current_time = start_time
    current_location = start_location
    count = 0
    itinerary = []
    for friend in perm:
        try:
            travel_time = travel_times[current_location][friend['location']]
        except KeyError:
            continue
        arrival = current_time + travel_time
        if arrival > friend['end']:
            continue
        start = max(arrival, friend['start'])
        if start + friend['duration'] > friend['end']:
            continue
        end_time = start + friend['duration']
        itinerary.append({
            'action': 'meet',
            'location': friend['location'],
            'person': friend['name'],
            'start_time': minutes_to_time(start),
            'end_time': minutes_to_time(end_time)
        })
        count += 1
        current_time = end_time
        current_location = friend['location']
        if count == 9:
            break
    if count > best_count:
        best_count = count
        best_itinerary = itinerary
        if best_count == 9:
            break

result = {"itinerary": best_itinerary}
print(json.dumps(result))