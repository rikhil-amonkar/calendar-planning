import json

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

travel_times = {
    "Haight-Ashbury": {
        "Russian Hill": 17,
        "Fisherman's Wharf": 23,
        "Nob Hill": 15,
        "Golden Gate Park": 7,
        "Alamo Square": 5,
        "Pacific Heights": 12
    },
    "Russian Hill": {
        "Haight-Ashbury": 17,
        "Fisherman's Wharf": 7,
        "Nob Hill": 5,
        "Golden Gate Park": 21,
        "Alamo Square": 15,
        "Pacific Heights": 7
    },
    "Fisherman's Wharf": {
        "Haight-Ashbury": 22,
        "Russian Hill": 7,
        "Nob Hill": 11,
        "Golden Gate Park": 25,
        "Alamo Square": 20,
        "Pacific Heights": 12
    },
    "Nob Hill": {
        "Haight-Ashbury": 13,
        "Russian Hill": 5,
        "Fisherman's Wharf": 11,
        "Golden Gate Park": 17,
        "Alamo Square": 11,
        "Pacific Heights": 8
    },
    "Golden Gate Park": {
        "Haight-Ashbury": 7,
        "Russian Hill": 19,
        "Fisherman's Wharf": 24,
        "Nob Hill": 20,
        "Alamo Square": 10,
        "Pacific Heights": 16
    },
    "Alamo Square": {
        "Haight-Ashbury": 5,
        "Russian Hill": 13,
        "Fisherman's Wharf": 19,
        "Nob Hill": 11,
        "Golden Gate Park": 9,
        "Pacific Heights": 10
    },
    "Pacific Heights": {
        "Haight-Ashbury": 11,
        "Russian Hill": 7,
        "Fisherman's Wharf": 13,
        "Nob Hill": 8,
        "Golden Gate Park": 15,
        "Alamo Square": 10
    }
}

friends = {
    'Steven': {
        'location': 'Golden Gate Park',
        'start': 510,
        'end': 1020,
        'min_duration': 75
    },
    'Anthony': {
        'location': 'Alamo Square',
        'start': 465,
        'end': 1185,
        'min_duration': 15
    },
    'Sandra': {
        'location': 'Pacific Heights',
        'start': 885,
        'end': 1305,
        'min_duration': 45
    },
    'Stephanie': {
        'location': 'Russian Hill',
        'start': 1200,
        'end': 1245,
        'min_duration': 15
    },
    'Kevin': {
        'location': "Fisherman's Wharf",
        'start': 1155,
        'end': 1305,
        'min_duration': 75
    }
}

order = ['Steven', 'Anthony', 'Sandra', 'Stephanie', 'Kevin']

itinerary = []
current_location = 'Haight-Ashbury'
current_time = 540  # 9:00 in minutes

for name in order:
    friend = friends[name]
    t = travel_times[current_location][friend['location']]
    travel_time = t

    if name == 'Stephanie':
        if current_time <= 1200 - travel_time:
            arrival_time = 1200
        else:
            arrival_time = current_time + travel_time
    else:
        arrival_time = current_time + travel_time

    if name == 'Stephanie':
        meeting_start = arrival_time
    else:
        meeting_start = max(arrival_time, friend['start'])
    
    meeting_end = meeting_start + friend['min_duration']
    
    itinerary.append({
        "action": "meet",
        "location": friend['location'],
        "person": name,
        "start_time": minutes_to_time(meeting_start),
        "end_time": minutes_to_time(meeting_end)
    })
    
    current_location = friend['location']
    current_time = meeting_end

result = {"itinerary": itinerary}
print(json.dumps(result))