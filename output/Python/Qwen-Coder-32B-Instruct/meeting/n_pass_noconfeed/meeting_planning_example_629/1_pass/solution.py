import json
from datetime import datetime, timedelta

# Define the travel times between locations
travel_times = {
    ('Russian Hill', 'Presidio'): 14,
    ('Russian Hill', 'Chinatown'): 9,
    ('Russian Hill', 'Pacific Heights'): 7,
    ('Russian Hill', 'Richmond District'): 14,
    ('Russian Hill', 'Fisherman\'s Wharf'): 7,
    ('Russian Hill', 'Golden Gate Park'): 21,
    ('Russian Hill', 'Bayview'): 23,
    ('Presidio', 'Russian Hill'): 14,
    ('Presidio', 'Chinatown'): 21,
    ('Presidio', 'Pacific Heights'): 11,
    ('Presidio', 'Richmond District'): 7,
    ('Presidio', 'Fisherman\'s Wharf'): 19,
    ('Presidio', 'Golden Gate Park'): 12,
    ('Presidio', 'Bayview'): 31,
    ('Chinatown', 'Russian Hill'): 7,
    ('Chinatown', 'Presidio'): 19,
    ('Chinatown', 'Pacific Heights'): 10,
    ('Chinatown', 'Richmond District'): 20,
    ('Chinatown', 'Fisherman\'s Wharf'): 8,
    ('Chinatown', 'Golden Gate Park'): 23,
    ('Chinatown', 'Bayview'): 22,
    ('Pacific Heights', 'Russian Hill'): 7,
    ('Pacific Heights', 'Presidio'): 11,
    ('Pacific Heights', 'Chinatown'): 11,
    ('Pacific Heights', 'Richmond District'): 12,
    ('Pacific Heights', 'Fisherman\'s Wharf'): 13,
    ('Pacific Heights', 'Golden Gate Park'): 15,
    ('Pacific Heights', 'Bayview'): 22,
    ('Richmond District', 'Russian Hill'): 13,
    ('Richmond District', 'Presidio'): 7,
    ('Richmond District', 'Chinatown'): 20,
    ('Richmond District', 'Pacific Heights'): 10,
    ('Richmond District', 'Fisherman\'s Wharf'): 18,
    ('Richmond District', 'Golden Gate Park'): 9,
    ('Richmond District', 'Bayview'): 26,
    ('Fisherman\'s Wharf', 'Russian Hill'): 7,
    ('Fisherman\'s Wharf', 'Presidio'): 17,
    ('Fisherman\'s Wharf', 'Chinatown'): 12,
    ('Fisherman\'s Wharf', 'Pacific Heights'): 12,
    ('Fisherman\'s Wharf', 'Richmond District'): 18,
    ('Fisherman\'s Wharf', 'Golden Gate Park'): 25,
    ('Fisherman\'s Wharf', 'Bayview'): 26,
    ('Golden Gate Park', 'Russian Hill'): 19,
    ('Golden Gate Park', 'Presidio'): 11,
    ('Golden Gate Park', 'Chinatown'): 23,
    ('Golden Gate Park', 'Pacific Heights'): 16,
    ('Golden Gate Park', 'Richmond District'): 7,
    ('Golden Gate Park', 'Fisherman\'s Wharf'): 24,
    ('Golden Gate Park', 'Bayview'): 23,
    ('Bayview', 'Russian Hill'): 23,
    ('Bayview', 'Presidio'): 31,
    ('Bayview', 'Chinatown'): 18,
    ('Bayview', 'Pacific Heights'): 23,
    ('Bayview', 'Richmond District'): 25,
    ('Bayview', 'Fisherman\'s Wharf'): 25,
    ('Bayview', 'Golden Gate Park'): 22,
}

# Define the meeting constraints
constraints = {
    'Matthew': {'location': 'Presidio', 'start': '11:00', 'end': '21:00', 'min_duration': 90},
    'Margaret': {'location': 'Chinatown', 'start': '9:15', 'end': '18:45', 'min_duration': 90},
    'Nancy': {'location': 'Pacific Heights', 'start': '14:15', 'end': '17:00', 'min_duration': 15},
    'Helen': {'location': 'Richmond District', 'start': '19:45', 'end': '22:00', 'min_duration': 60},
    'Rebecca': {'location': 'Fisherman\'s Wharf', 'start': '21:15', 'end': '22:15', 'min_duration': 60},
    'Kimberly': {'location': 'Golden Gate Park', 'start': '13:00', 'end': '16:30', 'min_duration': 120},
    'Kenneth': {'location': 'Bayview', 'start': '14:30', 'end': '18:00', 'min_duration': 60},
}

def parse_time(time_str):
    return datetime.strptime(time_str, '%H:%M')

def format_time(time_obj):
    return time_obj.strftime('%H:%M')

def can_meet(start, end, min_duration):
    return (end - start).total_seconds() / 60 >= min_duration

def find_optimal_schedule():
    start_time = parse_time('9:00')
    current_location = 'Russian Hill'
    itinerary = []

    def add_meeting(person, location, start, end):
        itinerary.append({
            "action": "meet",
            "location": location,
            "person": person,
            "start_time": format_time(start),
            "end_time": format_time(end)
        })

    # Sort constraints by start time
    sorted_constraints = sorted(constraints.items(), key=lambda x: parse_time(x[1]['start']))

    for person, details in sorted_constraints:
        location = details['location']
        start = parse_time(details['start'])
        end = parse_time(details['end'])
        min_duration = details['min_duration']

        # Calculate travel time from current location to meeting location
        travel_time = travel_times.get((current_location, location), float('inf'))
        arrival_time = start_time + timedelta(minutes=travel_time)

        # Check if we can meet within the available time
        if arrival_time < start:
            meeting_start = start
        elif arrival_time <= end:
            meeting_start = arrival_time
        else:
            continue

        meeting_end = meeting_start + timedelta(minutes=min_duration)

        # Ensure meeting ends before the person leaves
        if meeting_end <= end:
            add_meeting(person, location, meeting_start, meeting_end)
            start_time = meeting_end
            current_location = location

    return itinerary

optimal_itinerary = find_optimal_schedule()
result = {"itinerary": optimal_itinerary}
print(json.dumps(result))