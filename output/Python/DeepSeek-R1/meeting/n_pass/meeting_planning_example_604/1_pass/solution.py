import json

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

travel_times = {
    "Fisherman's Wharf": {
        "The Castro": 26,
        "Golden Gate Park": 25,
        "Embarcadero": 8,
        "Russian Hill": 7,
        "Nob Hill": 11,
        "Alamo Square": 20,
        "North Beach": 6
    },
    "The Castro": {
        "Fisherman's Wharf": 24,
        "Golden Gate Park": 11,
        "Embarcadero": 22,
        "Russian Hill": 18,
        "Nob Hill": 16,
        "Alamo Square": 8,
        "North Beach": 20
    },
    "Golden Gate Park": {
        "Fisherman's Wharf": 24,
        "The Castro": 13,
        "Embarcadero": 25,
        "Russian Hill": 19,
        "Nob Hill": 20,
        "Alamo Square": 10,
        "North Beach": 24
    },
    "Embarcadero": {
        "Fisherman's Wharf": 6,
        "The Castro": 25,
        "Golden Gate Park": 25,
        "Russian Hill": 8,
        "Nob Hill": 10,
        "Alamo Square": 19,
        "North Beach": 5
    },
    "Russian Hill": {
        "Fisherman's Wharf": 7,
        "The Castro": 21,
        "Golden Gate Park": 21,
        "Embarcadero": 8,
        "Nob Hill": 5,
        "Alamo Square": 15,
        "North Beach": 5
    },
    "Nob Hill": {
        "Fisherman's Wharf": 11,
        "The Castro": 17,
        "Golden Gate Park": 17,
        "Embarcadero": 9,
        "Russian Hill": 5,
        "Alamo Square": 11,
        "North Beach": 8
    },
    "Alamo Square": {
        "Fisherman's Wharf": 19,
        "The Castro": 8,
        "Golden Gate Park": 9,
        "Embarcadero": 17,
        "Russian Hill": 13,
        "Nob Hill": 11,
        "North Beach": 16
    },
    "North Beach": {
        "Fisherman's Wharf": 5,
        "The Castro": 22,
        "Golden Gate Park": 22,
        "Embarcadero": 6,
        "Russian Hill": 4,
        "Nob Hill": 7,
        "Alamo Square": 16
    }
}

friends = [
    {'name': 'Joseph', 'location': 'Alamo Square', 'start': 11*60+30, 'end': 12*60+45, 'min_duration': 15},
    {'name': 'Kimberly', 'location': 'North Beach', 'start': 15*60+45, 'end': 19*60+15, 'min_duration': 30},
    {'name': 'Karen', 'location': 'Russian Hill', 'start': 14*60+30, 'end': 19*60+45, 'min_duration': 30},
    {'name': 'Laura', 'location': 'The Castro', 'start': 19*60+45, 'end': 21*60+30, 'min_duration': 105}
]

current_location = "Fisherman's Wharf"
current_time = 9 * 60
itinerary = []

for friend in friends:
    travel_duration = travel_times[current_location][friend['location']]
    arrival_time = current_time + travel_duration
    start_meeting = max(arrival_time, friend['start'])
    end_meeting = start_meeting + friend['min_duration']
    if end_meeting > friend['end']:
        continue
    itinerary.append({
        "action": "meet",
        "location": friend['location'],
        "person": friend['name'],
        "start_time": minutes_to_time(start_meeting),
        "end_time": minutes_to_time(end_meeting)
    })
    current_location = friend['location']
    current_time = end_meeting

result = {"itinerary": itinerary}
print(json.dumps(result))