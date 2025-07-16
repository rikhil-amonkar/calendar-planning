import json
from itertools import permutations

def time_to_minutes(time_str):
    hours, minutes = map(int, time_str.split(':'))
    return hours * 60 + minutes

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

def calculate_schedule():
    travel_times = {
        'Chinatown': {
            'Mission District': 18,
            'Alamo Square': 17,
            'Pacific Heights': 10,
            'Union Square': 7,
            'Golden Gate Park': 23,
            'Sunset District': 29,
            'Presidio': 19
        },
        'Mission District': {
            'Chinatown': 16,
            'Alamo Square': 11,
            'Pacific Heights': 16,
            'Union Square': 15,
            'Golden Gate Park': 17,
            'Sunset District': 24,
            'Presidio': 25
        },
        'Alamo Square': {
            'Chinatown': 16,
            'Mission District': 10,
            'Pacific Heights': 10,
            'Union Square': 14,
            'Golden Gate Park': 9,
            'Sunset District': 16,
            'Presidio': 18
        },
        'Pacific Heights': {
            'Chinatown': 11,
            'Mission District': 15,
            'Alamo Square': 10,
            'Union Square': 12,
            'Golden Gate Park': 15,
            'Sunset District': 21,
            'Presidio': 11
        },
        'Union Square': {
            'Chinatown': 7,
            'Mission District': 14,
            'Alamo Square': 15,
            'Pacific Heights': 15,
            'Golden Gate Park': 22,
            'Sunset District': 26,
            'Presidio': 24
        },
        'Golden Gate Park': {
            'Chinatown': 23,
            'Mission District': 17,
            'Alamo Square': 10,
            'Pacific Heights': 16,
            'Union Square': 22,
            'Sunset District': 10,
            'Presidio': 11
        },
        'Sunset District': {
            'Chinatown': 30,
            'Mission District': 24,
            'Alamo Square': 17,
            'Pacific Heights': 21,
            'Union Square': 30,
            'Golden Gate Park': 11,
            'Presidio': 16
        },
        'Presidio': {
            'Chinatown': 21,
            'Mission District': 26,
            'Alamo Square': 18,
            'Pacific Heights': 11,
            'Union Square': 22,
            'Golden Gate Park': 12,
            'Sunset District': 15
        }
    }

    friends = [
        {'name': 'David', 'location': 'Mission District', 'start': '8:00', 'end': '19:45', 'duration': 45},
        {'name': 'Kenneth', 'location': 'Alamo Square', 'start': '14:00', 'end': '19:45', 'duration': 120},
        {'name': 'John', 'location': 'Pacific Heights', 'start': '17:00', 'end': '20:00', 'duration': 15},
        {'name': 'Charles', 'location': 'Union Square', 'start': '21:45', 'end': '22:45', 'duration': 60},
        {'name': 'Deborah', 'location': 'Golden Gate Park', 'start': '7:00', 'end': '18:15', 'duration': 90},
        {'name': 'Karen', 'location': 'Sunset District', 'start': '17:45', 'end': '21:15', 'duration': 15},
        {'name': 'Carol', 'location': 'Presidio', 'start': '8:15', 'end': '9:15', 'duration': 30}
    ]

    friend_names = [f['name'] for f in friends]
    best_schedule = None
    max_meetings = 0

    # Try all possible orders but limit permutations for performance
    for order in permutations(friend_names, min(5, len(friend_names))):  # Limit permutations
        current_location = 'Chinatown'
        current_time = time_to_minutes('9:00')
        schedule = []
        meetings = 0

        for name in order:
            friend = next(f for f in friends if f['name'] == name)
            travel_time = travel_times[current_location][friend['location']]
            arrival_time = current_time + travel_time
            start_window = time_to_minutes(friend['start'])
            end_window = time_to_minutes(friend['end'])

            # Add travel segment
            if current_location != friend['location']:
                schedule.append({
                    'action': 'travel',
                    'from': current_location,
                    'to': friend['location'],
                    'start_time': minutes_to_time(current_time),
                    'end_time': minutes_to_time(arrival_time),
                    'duration': travel_time
                })

            # Calculate meeting time
            meeting_start = max(arrival_time, start_window)
            meeting_end = meeting_start + friend['duration']

            if meeting_end > end_window:
                break  # Can't meet this friend, try next permutation

            schedule.append({
                'action': 'meet',
                'location': friend['location'],
                'person': friend['name'],
                'start_time': minutes_to_time(meeting_start),
                'end_time': minutes_to_time(meeting_end),
                'duration': friend['duration']
            })
            
            meetings += 1
            current_time = meeting_end
            current_location = friend['location']

        if meetings > max_meetings or (meetings == max_meetings and best_schedule is None):
            max_meetings = meetings
            best_schedule = schedule

    return {'itinerary': best_schedule if best_schedule else []}

result = calculate_schedule()
print(json.dumps(result, indent=2))