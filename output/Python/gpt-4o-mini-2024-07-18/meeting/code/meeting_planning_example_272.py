import json
from datetime import datetime, timedelta

# Travel distances in minutes
travel_times = {
    ('Russian Hill', 'Nob Hill'): 5,
    ('Russian Hill', 'Mission District'): 16,
    ('Russian Hill', 'Embarcadero'): 8,
    ('Nob Hill', 'Russian Hill'): 5,
    ('Nob Hill', 'Mission District'): 13,
    ('Nob Hill', 'Embarcadero'): 9,
    ('Mission District', 'Russian Hill'): 15,
    ('Mission District', 'Nob Hill'): 12,
    ('Mission District', 'Embarcadero'): 19,
    ('Embarcadero', 'Russian Hill'): 8,
    ('Embarcadero', 'Nob Hill'): 10,
    ('Embarcadero', 'Mission District'): 20,
}

# Meeting constraints
participants = {
    'Patricia': {
        'location': 'Nob Hill',
        'available_from': '18:30',
        'available_to': '21:45',
        'min_meeting_duration': 90
    },
    'Ashley': {
        'location': 'Mission District',
        'available_from': '20:30',
        'available_to': '21:15',
        'min_meeting_duration': 45
    },
    'Timothy': {
        'location': 'Embarcadero',
        'available_from': '09:45',
        'available_to': '17:45',
        'min_meeting_duration': 120
    },
}

arrival_time = '09:00'
departure_time = '21:45'

# Function to convert time strings to datetime objects
def time_to_datetime(time_str):
    return datetime.strptime(time_str, '%H:%M')

# Function to compute end time based on start time and duration
def compute_end_time(start_time, duration):
    return start_time + timedelta(minutes=duration)

# Generate meeting schedule
schedule = []
current_time = time_to_datetime(arrival_time)

# Schedule for Timothy
timothy_start = time_to_datetime(participants['Timothy']['available_from'])
timothy_end = time_to_datetime(participants['Timothy']['available_to'])

# Try to meet Timothy first
if current_time < timothy_start:
    current_time = timothy_start

timothy_meeting_duration = participants['Timothy']['min_meeting_duration']
timothy_meeting_end = compute_end_time(current_time, timothy_meeting_duration)

if timothy_meeting_end <= timothy_end:
    schedule.append({
        "action": "meet",
        "location": participants['Timothy']['location'],
        "person": "Timothy",
        "start_time": current_time.strftime('%H:%M'),
        "end_time": timothy_meeting_end.strftime('%H:%M')
    })
    current_time = timothy_meeting_end + timedelta(minutes=travel_times[('Embarcadero', 'Nob Hill')])

# Schedule for Patricia
patricia_start = time_to_datetime(participants['Patricia']['available_from'])
patricia_end = time_to_datetime(participants['Patricia']['available_to'])

if current_time < patricia_start:
    current_time = patricia_start

patricia_meeting_duration = participants['Patricia']['min_meeting_duration']
patricia_meeting_end = compute_end_time(current_time, patricia_meeting_duration)

if patricia_meeting_end <= patricia_end:
    schedule.append({
        "action": "meet",
        "location": participants['Patricia']['location'],
        "person": "Patricia",
        "start_time": current_time.strftime('%H:%M'),
        "end_time": patricia_meeting_end.strftime('%H:%M'),
    })
    current_time = patricia_meeting_end + timedelta(minutes=travel_times[('Nob Hill', 'Mission District')])

# Schedule for Ashley
ashley_start = time_to_datetime(participants['Ashley']['available_from'])
ashley_end = time_to_datetime(participants['Ashley']['available_to'])

if current_time < ashley_start:
    current_time = ashley_start

ashley_meeting_duration = participants['Ashley']['min_meeting_duration']
ashley_meeting_end = compute_end_time(current_time, ashley_meeting_duration)

if ashley_meeting_end <= ashley_end:
    schedule.append({
        "action": "meet",
        "location": participants['Ashley']['location'],
        "person": "Ashley",
        "start_time": current_time.strftime('%H:%M'),
        "end_time": ashley_meeting_end.strftime('%H:%M'),
    })

# Output the schedule as a JSON formatted dictionary
output = {"itinerary": schedule}
print(json.dumps(output, indent=2))