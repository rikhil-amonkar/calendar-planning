import itertools
import json

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

friends = [
    {
        'name': 'Elizabeth',
        'location': 'Mission District',
        'available_start': 630,
        'available_end': 1200,
        'required_duration': 90
    },
    {
        'name': 'David',
        'location': 'Union Square',
        'available_start': 915,
        'available_end': 1140,
        'required_duration': 45
    },
    {
        'name': 'Sandra',
        'location': 'Pacific Heights',
        'available_start': 420,
        'available_end': 1200,
        'required_duration': 120
    },
    {
        'name': 'Thomas',
        'location': 'Bayview',
        'available_start': 1170,
        'available_end': 1230,
        'required_duration': 30
    },
    {
        'name': 'Robert',
        'location': "Fisherman's Wharf",
        'available_start': 600,
        'available_end': 900,
        'required_duration': 15
    },
    {
        'name': 'Kenneth',
        'location': 'Marina District',
        'available_start': 645,
        'available_end': 780,
        'required_duration': 45
    },
    {
        'name': 'Melissa',
        'location': 'Richmond District',
        'available_start': 1095,
        'available_end': 1200,
        'required_duration': 15
    },
    {
        'name': 'Kimberly',
        'location': 'Sunset District',
        'available_start': 615,
        'available_end': 1095,
        'required_duration': 105
    },
    {
        'name': 'Amanda',
        'location': 'Golden Gate Park',
        'available_start': 465,
        'available_end': 1125,
        'required_duration': 15
    }
]

travel_times = {
    'Haight-Ashbury': {
        'Mission District': 11,
        'Union Square': 19,
        'Pacific Heights': 12,
        'Bayview': 18,
        "Fisherman's Wharf": 23,
        'Marina District': 17,
        'Richmond District': 10,
        'Sunset District': 15,
        'Golden Gate Park': 7
    },
    'Mission District': {
        'Haight-Ashbury': 12,
        'Union Square': 15,
        'Pacific Heights': 16,
        'Bayview': 14,
        "Fisherman's Wharf": 22,
        'Marina District': 19,
        'Richmond District': 20,
        'Sunset District': 24,
        'Golden Gate Park': 17
    },
    'Union Square': {
        'Haight-Ashbury': 18,
        'Mission District': 14,
        'Pacific Heights': 15,
        'Bayview': 15,
        "Fisherman's Wharf": 15,
        'Marina District': 18,
        'Richmond District': 20,
        'Sunset District': 27,
        'Golden Gate Park': 22
    },
    'Pacific Heights': {
        'Haight-Ashbury': 11,
        'Mission District': 15,
        'Union Square': 12,
        'Bayview': 22,
        "Fisherman's Wharf": 13,
        'Marina District': 6,
        'Richmond District': 12,
        'Sunset District': 21,
        'Golden Gate Park': 15
    },
    'Bayview': {
        'Haight-Ashbury': 19,
        'Mission District': 13,
        'Union Square': 18,
        'Pacific Heights': 23,
        "Fisherman's Wharf": 25,
        'Marina District': 27,
        'Richmond District': 25,
        'Sunset District': 23,
        'Golden Gate Park': 22
    },
    "Fisherman's Wharf": {
        'Haight-Ashbury': 22,
        'Mission District': 22,
        'Union Square': 13,
        'Pacific Heights': 12,
        'Bayview': 26,
        'Marina District': 9,
        'Richmond District': 18,
        'Sunset District': 27,
        'Golden Gate Park': 25
    },
    'Marina District': {
        'Haight-Ashbury': 16,
        'Mission District': 20,
        'Union Square': 16,
        'Pacific Heights': 7,
        'Bayview': 27,
        "Fisherman's Wharf": 10,
        'Richmond District': 11,
        'Sunset District': 19,
        'Golden Gate Park': 18
    },
    'Richmond District': {
        'Haight-Ashbury': 10,
        'Mission District': 20,
        'Union Square': 21,
        'Pacific Heights': 10,
        'Bayview': 27,
        "Fisherman's Wharf": 18,
        'Marina District': 9,
        'Sunset District': 11,
        'Golden Gate Park': 9
    },
    'Sunset District': {
        'Haight-Ashbury': 15,
        'Mission District': 25,
        'Union Square': 30,
        'Pacific Heights': 21,
        'Bayview': 22,
        "Fisherman's Wharf": 29,
        'Marina District': 21,
        'Richmond District': 12,
        'Golden Gate Park': 11
    },
    'Golden Gate Park': {
        'Haight-Ashbury': 7,
        'Mission District': 17,
        'Union Square': 22,
        'Pacific Heights': 16,
        'Bayview': 23,
        "Fisherman's Wharf": 24,
        'Marina District': 16,
        'Richmond District': 7,
        'Sunset District': 10
    }
}

def get_travel_time(origin, destination):
    return travel_times[origin][destination]

def compute_itinerary(perm):
    current_time = 540  # 9:00 AM in minutes
    current_location = 'Haight-Ashbury'
    itinerary = []
    for friend in perm:
        try:
            travel_time = get_travel_time(current_location, friend['location'])
        except KeyError:
            return []
        arrival_time = current_time + travel_time
        meeting_start = max(arrival_time, friend['available_start'])
        meeting_end = meeting_start + friend['required_duration']
        if meeting_end > friend['available_end']:
            break
        itinerary.append( (friend, meeting_start, meeting_end) )
        current_time = meeting_end
        current_location = friend['location']
    return itinerary

best_itinerary = []
max_length = 0

for perm in itertools.permutations(friends):
    itinerary = compute_itinerary(perm)
    if len(itinerary) > max_length:
        max_length = len(itinerary)
        best_itinerary = itinerary
        if max_length == len(friends):
            break

itinerary_list = []
for entry in best_itinerary:
    friend, start, end = entry
    start_time = minutes_to_time(start)
    end_time = minutes_to_time(end)
    itinerary_list.append({
        "action": "meet",
        "location": friend['location'],
        "person": friend['name'],
        "start_time": start_time,
        "end_time": end_time
    })

result = {"itinerary": itinerary_list}

print(json.dumps(result, indent=2))