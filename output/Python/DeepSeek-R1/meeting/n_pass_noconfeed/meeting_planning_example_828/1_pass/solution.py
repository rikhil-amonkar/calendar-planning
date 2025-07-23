import itertools
import json

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

# Define friends with their constraints
friends = [
    {"name": "Stephanie", "location": "Richmond District", "start": 16*60+15, "end": 21*60+30, "min_duration": 75},
    {"name": "William", "location": "Union Square", "start": 10*60+45, "end": 17*60+30, "min_duration": 45},
    {"name": "Elizabeth", "location": "Nob Hill", "start": 12*60+15, "end": 15*60+0, "min_duration": 105},
    {"name": "Joseph", "location": "Fisherman's Wharf", "start": 12*60+45, "end": 14*60+0, "min_duration": 75},
    {"name": "Anthony", "location": "Golden Gate Park", "start": 13*60+0, "end": 20*60+30, "min_duration": 75},
    {"name": "Barbara", "location": "Embarcadero", "start": 19*60+15, "end": 20*60+30, "min_duration": 75},
    {"name": "Carol", "location": "Financial District", "start": 11*60+45, "end": 16*60+15, "min_duration": 60},
    {"name": "Sandra", "location": "North Beach", "start": 10*60+0, "end": 12*60+30, "min_duration": 15},
    {"name": "Kenneth", "location": "Presidio", "start": 21*60+15, "end": 22*60+15, "min_duration": 45}
]

# Define travel times between districts
travel_time = {
    "Marina District": {
        "Richmond District": 11,
        "Union Square": 16,
        "Nob Hill": 12,
        "Fisherman's Wharf": 10,
        "Golden Gate Park": 18,
        "Embarcadero": 14,
        "Financial District": 17,
        "North Beach": 11,
        "Presidio": 10
    },
    "Richmond District": {
        "Marina District": 9,
        "Union Square": 21,
        "Nob Hill": 17,
        "Fisherman's Wharf": 18,
        "Golden Gate Park": 9,
        "Embarcadero": 19,
        "Financial District": 22,
        "North Beach": 17,
        "Presidio": 7
    },
    "Union Square": {
        "Marina District": 18,
        "Richmond District": 20,
        "Nob Hill": 9,
        "Fisherman's Wharf": 15,
        "Golden Gate Park": 22,
        "Embarcadero": 11,
        "Financial District": 9,
        "North Beach": 10,
        "Presidio": 24
    },
    "Nob Hill": {
        "Marina District": 11,
        "Richmond District": 14,
        "Union Square": 7,
        "Fisherman's Wharf": 10,
        "Golden Gate Park": 17,
        "Embarcadero": 9,
        "Financial District": 9,
        "North Beach": 8,
        "Presidio": 17
    },
    "Fisherman's Wharf": {
        "Marina District": 9,
        "Richmond District": 18,
        "Union Square": 13,
        "Nob Hill": 11,
        "Golden Gate Park": 25,
        "Embarcadero": 8,
        "Financial District": 11,
        "North Beach": 6,
        "Presidio": 17
    },
    "Golden Gate Park": {
        "Marina District": 16,
        "Richmond District": 7,
        "Union Square": 22,
        "Nob Hill": 20,
        "Fisherman's Wharf": 24,
        "Embarcadero": 25,
        "Financial District": 26,
        "North Beach": 23,
        "Presidio": 11
    },
    "Embarcadero": {
        "Marina District": 12,
        "Richmond District": 21,
        "Union Square": 10,
        "Nob Hill": 10,
        "Fisherman's Wharf": 6,
        "Golden Gate Park": 25,
        "Financial District": 5,
        "North Beach": 5,
        "Presidio": 20
    },
    "Financial District": {
        "Marina District": 15,
        "Richmond District": 21,
        "Union Square": 9,
        "Nob Hill": 8,
        "Fisherman's Wharf": 10,
        "Golden Gate Park": 23,
        "Embarcadero": 4,
        "North Beach": 7,
        "Presidio": 22
    },
    "North Beach": {
        "Marina District": 9,
        "Richmond District": 18,
        "Union Square": 7,
        "Nob Hill": 7,
        "Fisherman's Wharf": 5,
        "Golden Gate Park": 22,
        "Embarcadero": 6,
        "Financial District": 8,
        "Presidio": 17
    },
    "Presidio": {
        "Marina District": 11,
        "Richmond District": 7,
        "Union Square": 22,
        "Nob Hill": 18,
        "Fisherman's Wharf": 19,
        "Golden Gate Park": 12,
        "Embarcadero": 20,
        "Financial District": 23,
        "North Beach": 18
    }
}

max_end_time = 22*60+15  # Kenneth's end time (22:15) in minutes

best_count = 0
best_itinerary = None

for perm in itertools.permutations(friends):
    current_time = 540  # 9:00 in minutes
    current_location = "Marina District"
    itinerary = []
    count = 0
    for friend in perm:
        if current_time > max_end_time:
            break
        if current_location == friend['location']:
            time_to_travel = 0
        else:
            time_to_travel = travel_time[current_location][friend['location']]
        arrival = current_time + time_to_travel
        start_meeting = max(arrival, friend['start'])
        if start_meeting + friend['min_duration'] <= friend['end']:
            end_meeting = start_meeting + friend['min_duration']
            itinerary.append({
                "action": "meet",
                "location": friend['location'],
                "person": friend['name'],
                "start_time": minutes_to_time(start_meeting),
                "end_time": minutes_to_time(end_meeting)
            })
            count += 1
            current_time = end_meeting
            current_location = friend['location']
        else:
            current_time = arrival
            current_location = friend['location']
    if count > best_count:
        best_count = count
        best_itinerary = itinerary

# Output the best itinerary as JSON
output = {"itinerary": best_itinerary}
print(json.dumps(output, indent=2))