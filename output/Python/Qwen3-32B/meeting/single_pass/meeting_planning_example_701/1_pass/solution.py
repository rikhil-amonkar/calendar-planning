import itertools
import json

def to_time_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

travel_times = {
    'Mission District': {
        'The Castro': 7,
        'Nob Hill': 12,
        'Presidio': 25,
        'Marina District': 19,
        'Pacific Heights': 16,
        'Golden Gate Park': 17,
        'Chinatown': 16,
        'Richmond District': 20,
    },
    'The Castro': {
        'Mission District': 7,
        'Nob Hill': 16,
        'Presidio': 20,
        'Marina District': 21,
        'Pacific Heights': 16,
        'Golden Gate Park': 11,
        'Chinatown': 22,
        'Richmond District': 16,
    },
    'Nob Hill': {
        'Mission District': 13,
        'The Castro': 17,
        'Presidio': 17,
        'Marina District': 11,
        'Pacific Heights': 8,
        'Golden Gate Park': 17,
        'Chinatown': 6,
        'Richmond District': 14,
    },
    'Presidio': {
        'Mission District': 26,
        'The Castro': 21,
        'Nob Hill': 18,
        'Marina District': 11,
        'Pacific Heights': 11,
        'Golden Gate Park': 12,
        'Chinatown': 21,
        'Richmond District': 7,
    },
    'Marina District': {
        'Mission District': 20,
        'The Castro': 22,
        'Nob Hill': 12,
        'Presidio': 10,
        'Pacific Heights': 7,
        'Golden Gate Park': 18,
        'Chinatown': 15,
        'Richmond District': 11,
    },
    'Pacific Heights': {
        'Mission District': 15,
        'The Castro': 16,
        'Nob Hill': 8,
        'Presidio': 11,
        'Marina District': 6,
        'Golden Gate Park': 15,
        'Chinatown': 11,
        'Richmond District': 12,
    },
    'Golden Gate Park': {
        'Mission District': 17,
        'The Castro': 13,
        'Nob Hill': 20,
        'Presidio': 11,
        'Marina District': 16,
        'Pacific Heights': 16,
        'Chinatown': 23,
        'Richmond District': 7,
    },
    'Chinatown': {
        'Mission District': 17,
        'The Castro': 22,
        'Nob Hill': 9,
        'Presidio': 19,
        'Marina District': 12,
        'Pacific Heights': 10,
        'Golden Gate Park': 23,
        'Richmond District': 20,
    },
    'Richmond District': {
        'Mission District': 20,
        'The Castro': 16,
        'Nob Hill': 17,
        'Presidio': 7,
        'Marina District': 9,
        'Pacific Heights': 10,
        'Golden Gate Park': 9,
        'Chinatown': 20,
    },
}

friends = [
    {
        'name': 'Daniel',
        'location': 'Nob Hill',
        'start_time': 8 * 60 + 15,  # 8:15 AM
        'end_time': 11 * 60 + 0,    # 11:00 AM
        'min_duration': 15
    },
    {
        'name': 'Elizabeth',
        'location': 'Presidio',
        'start_time': 21 * 60 + 15,  # 9:15 PM
        'end_time': 22 * 60 + 15,    # 10:15 PM
        'min_duration': 45
    },
    {
        'name': 'Steven',
        'location': 'Marina District',
        'start_time': 16 * 60 + 30,  # 4:30 PM
        'end_time': 20 * 60 + 45,    # 8:45 PM
        'min_duration': 90
    },
    {
        'name': 'Timothy',
        'location': 'Pacific Heights',
        'start_time': 12 * 60 + 0,   # 12:00 PM
        'end_time': 18 * 60 + 0,     # 6:00 PM
        'min_duration': 90
    },
    {
        'name': 'Kevin',
        'location': 'Chinatown',
        'start_time': 12 * 60 + 0,   # 12:00 PM
        'end_time': 19 * 60 + 0,     # 7:00 PM
        'min_duration': 30
    },
    {
        'name': 'Betty',
        'location': 'Richmond District',
        'start_time': 13 * 60 + 15,  # 1:15 PM
        'end_time': 15 * 60 + 45,    # 3:45 PM
        'min_duration': 30
    },
    {
        'name': 'Ashley',
        'location': 'Golden Gate Park',
        'start_time': 20 * 60 + 45,  # 8:45 PM
        'end_time': 21 * 60 + 45,    # 9:45 PM
        'min_duration': 60
    },
    {
        'name': 'Lisa',
        'location': 'The Castro',
        'start_time': 19 * 60 + 15,  # 7:15 PM
        'end_time': 21 * 60 + 15,    # 9:15 PM
        'min_duration': 120
    }
]

best_itinerary = []
max_count = 0

for perm in itertools.permutations(friends):
    current_time = 9 * 60  # 9:00 AM
    current_location = 'Mission District'
    itinerary = []
    
    for friend in perm:
        dest = friend['location']
        if current_location not in travel_times or dest not in travel_times[current_location]:
            continue
        travel_time = travel_times[current_location][dest]
        arrival_time = current_time + travel_time

        start_meet = max(arrival_time, friend['start_time'])
        end_meet = start_meet + friend['min_duration']

        if end_meet <= friend['end_time']:
            itinerary.append({
                'action': 'meet',
                'location': dest,
                'person': friend['name'],
                'start_time': to_time_str(start_meet),
                'end_time': to_time_str(end_meet)
            })
            current_time = end_meet
            current_location = dest
    
    if len(itinerary) > max_count:
        max_count = len(itinerary)
        best_itinerary = itinerary
    elif len(itinerary) == max_count and max_count > 0:
        # Tie: choose the one with earliest end time?
        # For simplicity, we'll keep the first one found
        pass

result = {
    "itinerary": best_itinerary
}

print(json.dumps(result, indent=2))