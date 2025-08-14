import json
from itertools import permutations

def mins_to_time(m):
    hours = m // 60
    minutes = m % 60
    return f"{hours}:{minutes:02d}"

travel_times = {
    'Pacific Heights': {
        'Presidio': 11,
        'Marina District': 6
    },
    'Presidio': {
        'Pacific Heights': 11,
        'Marina District': 10
    },
    'Marina District': {
        'Pacific Heights': 7,
        'Presidio': 10
    }
}

people = [
    {
        'name': 'Jason',
        'location': 'Presidio',
        'available_start': 600,  # 10:00 AM
        'available_end': 975,    # 4:15 PM
        'min_duration': 90
    },
    {
        'name': 'Kenneth',
        'location': 'Marina District',
        'available_start': 930,  # 3:30 PM
        'available_end': 1005,   # 4:45 PM
        'min_duration': 45
    }
]

start_time_mins = 540  # 9:00 AM

def simulate_sequence(sequence):
    current_time = start_time_mins
    current_location = 'Pacific Heights'
    meetings = []
    for person in sequence:
        travel_time = travel_times[current_location][person['location']]
        current_time += travel_time
        available_start = person['available_start']
        available_end = person['available_end']
        min_duration = person['min_duration']
        start = max(current_time, available_start)
        end = start + min_duration
        if end > available_end:
            return None
        meetings.append({
            'action': 'meet',
            'location': person['location'],
            'person': person['name'],
            'start_time': start,
            'end_time': end
        })
        current_time = end
        current_location = person['location']
    return meetings

best_meetings = []
for seq in permutations(people):
    meetings = simulate_sequence(seq)
    if meetings:
        if len(meetings) > len(best_meetings):
            best_meetings = meetings

itinerary = []
for meet in best_meetings:
    itinerary.append({
        'action': meet['action'],
        'location': meet['location'],
        'person': meet['person'],
        'start_time': mins_to_time(meet['start_time']),
        'end_time': mins_to_time(meet['end_time'])
    })

result = {
    'itinerary': itinerary
}

print(json.dumps(result, indent=2))