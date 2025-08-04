import json
from datetime import datetime, timedelta

# Define travel times
travel_times = {
    ('Union Square', 'Golden Gate Park'): 22,
    ('Union Square', 'Pacific Heights'): 15,
    ('Union Square', 'Presidio'): 24,
    ('Union Square', 'Chinatown'): 7,
    ('Union Square', 'The Castro'): 19,
    ('Golden Gate Park', 'Union Square'): 22,
    ('Golden Gate Park', 'Pacific Heights'): 16,
    ('Golden Gate Park', 'Presidio'): 11,
    ('Golden Gate Park', 'Chinatown'): 23,
    ('Golden Gate Park', 'The Castro'): 13,
    ('Pacific Heights', 'Union Square'): 12,
    ('Pacific Heights', 'Golden Gate Park'): 15,
    ('Pacific Heights', 'Presidio'): 11,
    ('Pacific Heights', 'Chinatown'): 11,
    ('Pacific Heights', 'The Castro'): 16,
    ('Presidio', 'Union Square'): 22,
    ('Presidio', 'Golden Gate Park'): 12,
    ('Presidio', 'Pacific Heights'): 11,
    ('Presidio', 'Chinatown'): 21,
    ('Presidio', 'The Castro'): 21,
    ('Chinatown', 'Union Square'): 7,
    ('Chinatown', 'Golden Gate Park'): 23,
    ('Chinatown', 'Pacific Heights'): 11,
    ('Chinatown', 'Presidio'): 19,
    ('Chinatown', 'The Castro'): 22,
    ('The Castro', 'Union Square'): 19,
    ('The Castro', 'Golden Gate Park'): 11,
    ('The Castro', 'Pacific Heights'): 16,
    ('The Castro', 'Presidio'): 20,
    ('The Castro', 'Chinatown'): 20,
}

# Define meeting constraints
meetings = {
    'Andrew': {'location': 'Golden Gate Park', 'start': '11:45', 'end': '14:30', 'min_duration': 75},
    'Sarah': {'location': 'Pacific Heights', 'start': '16:15', 'end': '18:45', 'min_duration': 15},
    'Nancy': {'location': 'Presidio', 'start': '17:30', 'end': '19:15', 'min_duration': 60},
    'Rebecca': {'location': 'Chinatown', 'start': '9:45', 'end': '21:30', 'min_duration': 90},
    'Robert': {'location': 'The Castro', 'start': '8:30', 'end': '14:15', 'min_duration': 30},
}

# Convert times to datetime objects
def time_to_dt(time_str):
    return datetime.strptime(time_str, '%H:%M')

# Check if a meeting can fit within the available time
def can_meet(start, end, min_duration):
    return (time_to_dt(end) - time_to_dt(start)).total_seconds() / 60 >= min_duration

# Calculate the next possible meeting time after traveling
def next_meeting_time(current_time, current_location, location, person):
    travel_time = travel_times[(current_location, location)]
    next_time = current_time + timedelta(minutes=travel_time)
    meeting_start = time_to_dt(meetings[person]['start'])
    meeting_end = time_to_dt(meetings[person]['end'])
    if next_time < meeting_start:
        next_time = meeting_start
    if next_time + timedelta(minutes=meetings[person]['min_duration']) <= meeting_end:
        return next_time
    return None

# Find the optimal schedule
def find_optimal_schedule():
    current_time = time_to_dt('9:00')
    current_location = 'Union Square'
    itinerary = []

    while current_time < time_to_dt('21:30'):
        best_meeting = None
        best_time = None
        for person, details in meetings.items():
            if person not in [entry['person'] for entry in itinerary]:
                meeting_time = next_meeting_time(current_time, current_location, details['location'], person)
                if meeting_time:
                    if best_time is None or meeting_time < best_time:
                        best_meeting = person
                        best_time = meeting_time
        
        if best_meeting:
            location = meetings[best_meeting]['location']
            start_time = best_time
            end_time = start_time + timedelta(minutes=meetings[best_meeting]['min_duration'])
            itinerary.append({
                'action': 'meet',
                'location': location,
                'person': best_meeting,
                'start_time': start_time.strftime('%H:%M'),
                'end_time': end_time.strftime('%H:%M')
            })
            current_time = end_time
            current_location = location
        else:
            break

    return itinerary

# Generate the result
result = {
    'itinerary': find_optimal_schedule()
}

# Output the result as JSON
print(json.dumps(result))