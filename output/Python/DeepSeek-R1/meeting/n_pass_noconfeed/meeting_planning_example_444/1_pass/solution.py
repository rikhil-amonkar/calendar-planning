import json

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02}"

travel_times = {
    'Financial District': {
        'Russian Hill': 10,
        'Sunset District': 31,
        'North Beach': 7,
        'The Castro': 23,
        'Golden Gate Park': 23
    },
    'Russian Hill': {
        'Financial District': 11,
        'Sunset District': 23,
        'North Beach': 5,
        'The Castro': 21,
        'Golden Gate Park': 21
    },
    'Sunset District': {
        'Financial District': 30,
        'Russian Hill': 24,
        'North Beach': 29,
        'The Castro': 17,
        'Golden Gate Park': 11
    },
    'North Beach': {
        'Financial District': 8,
        'Russian Hill': 4,
        'Sunset District': 27,
        'The Castro': 22,
        'Golden Gate Park': 22
    },
    'The Castro': {
        'Financial District': 20,
        'Russian Hill': 18,
        'Sunset District': 17,
        'North Beach': 20,
        'Golden Gate Park': 11
    },
    'Golden Gate Park': {
        'Financial District': 26,
        'Russian Hill': 19,
        'Sunset District': 10,
        'North Beach': 24,
        'The Castro': 13
    }
}

itinerary = []

current_time = 540
current_location = 'Financial District'

next_location = 'Sunset District'
travel_time = travel_times[current_location][next_location]
current_time += travel_time
meeting_start = current_time
meeting_end = meeting_start + 60
itinerary.append({
    "action": "meet",
    "location": next_location,
    "person": "Patricia",
    "start_time": minutes_to_time(meeting_start),
    "end_time": minutes_to_time(meeting_end)
})

current_time = 721
current_location = 'Sunset District'
next_location = 'North Beach'
travel_time = travel_times[current_location][next_location]
current_time += travel_time
meeting_start = current_time
meeting_end = meeting_start + 15
itinerary.append({
    "action": "meet",
    "location": next_location,
    "person": "Laura",
    "start_time": minutes_to_time(meeting_start),
    "end_time": minutes_to_time(meeting_end)
})

current_time = meeting_end
current_location = 'North Beach'
next_location = 'Russian Hill'
travel_time = travel_times[current_location][next_location]
current_time += travel_time
meeting_start = 825
meeting_end = meeting_start + 105
itinerary.append({
    "action": "meet",
    "location": next_location,
    "person": "Ronald",
    "start_time": minutes_to_time(meeting_start),
    "end_time": minutes_to_time(meeting_end)
})

current_time = meeting_end
current_location = 'Russian Hill'
next_location = 'The Castro'
travel_time = travel_times[current_location][next_location]
current_time += travel_time
meeting_start = 975
meeting_end = meeting_start + 60
itinerary.append({
    "action": "meet",
    "location": next_location,
    "person": "Emily",
    "start_time": minutes_to_time(meeting_start),
    "end_time": minutes_to_time(meeting_end)
})

result = {"itinerary": itinerary}
print(json.dumps(result))