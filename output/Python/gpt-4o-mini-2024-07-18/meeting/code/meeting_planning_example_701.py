import json
from datetime import datetime, timedelta

# Travel distances (in minutes)
travel_times = {
    ('Mission District', 'The Castro'): 7,
    ('Mission District', 'Nob Hill'): 12,
    ('Mission District', 'Presidio'): 25,
    ('Mission District', 'Marina District'): 19,
    ('Mission District', 'Pacific Heights'): 16,
    ('Mission District', 'Golden Gate Park'): 17,
    ('Mission District', 'Chinatown'): 16,
    ('Mission District', 'Richmond District'): 20,
    ('The Castro', 'Nob Hill'): 16,
    ('The Castro', 'Presidio'): 20,
    ('The Castro', 'Marina District'): 21,
    ('The Castro', 'Pacific Heights'): 16,
    ('The Castro', 'Golden Gate Park'): 11,
    ('The Castro', 'Chinatown'): 22,
    ('The Castro', 'Richmond District'): 16,
    ('Nob Hill', 'Presidio'): 17,
    ('Nob Hill', 'Marina District'): 11,
    ('Nob Hill', 'Pacific Heights'): 8,
    ('Nob Hill', 'Golden Gate Park'): 17,
    ('Nob Hill', 'Chinatown'): 6,
    ('Nob Hill', 'Richmond District'): 14,
    ('Presidio', 'Marina District'): 11,
    ('Presidio', 'Pacific Heights'): 11,
    ('Presidio', 'Golden Gate Park'): 12,
    ('Presidio', 'Chinatown'): 21,
    ('Presidio', 'Richmond District'): 7,
    ('Marina District', 'Pacific Heights'): 6,
    ('Marina District', 'Golden Gate Park'): 18,
    ('Marina District', 'Chinatown'): 15,
    ('Marina District', 'Richmond District'): 11,
    ('Pacific Heights', 'Golden Gate Park'): 15,
    ('Pacific Heights', 'Chinatown'): 11,
    ('Golden Gate Park', 'Chinatown'): 23,
}

# Meeting constraints
meetings = {
    'Lisa': {'location': 'The Castro', 'start': '19:15', 'end': '21:15', 'duration': 120},
    'Daniel': {'location': 'Nob Hill', 'start': '08:15', 'end': '11:00', 'duration': 15},
    'Elizabeth': {'location': 'Presidio', 'start': '21:15', 'end': '22:15', 'duration': 45},
    'Steven': {'location': 'Marina District', 'start': '16:30', 'end': '20:45', 'duration': 90},
    'Timothy': {'location': 'Pacific Heights', 'start': '12:00', 'end': '18:00', 'duration': 90},
    'Ashley': {'location': 'Golden Gate Park', 'start': '20:45', 'end': '21:45', 'duration': 60},
    'Kevin': {'location': 'Chinatown', 'start': '12:00', 'end': '19:00', 'duration': 30},
    'Betty': {'location': 'Richmond District', 'start': '13:15', 'end': '15:45', 'duration': 30},
}

# Initial time in Mission District
start_time = datetime.strptime("09:00", "%H:%M")
itinerary = []

# Function to add meeting to itinerary
def add_meeting(person, location, start, duration):
    end = start + timedelta(minutes=duration)
    itinerary.append({
        "action": "meet",
        "location": location,
        "person": person,
        "start_time": start.strftime("%H:%M"),
        "end_time": end.strftime("%H:%M"),
    })
    return end

current_time = start_time

# Function to compute schedule considering all constraints
for person, details in meetings.items():
    location = details['location']
    duration = details['duration']
    start_window = datetime.strptime(details['start'], "%H:%M")
    end_window = datetime.strptime(details['end'], "%H:%M")

    travel_back = travel_times.get(('Mission District', location), 0)
    travel_to = travel_times.get((location, 'Mission District'), 0)

    # Check meeting time in the window
    if current_time < start_window:
        current_time = start_window

    if current_time + timedelta(minutes=duration + travel_back) > end_window:
        continue  # Not enough time for this meeting

    # Move to the location for the meeting
    current_time += timedelta(minutes=travel_back)

    # Schedule the meeting
    current_time = add_meeting(person, location, current_time, duration)

    # Travel back to Mission District
    current_time += timedelta(minutes=travel_to)

# Output the resulting itinerary in JSON format
result = {
    "itinerary": itinerary
}

print(json.dumps(result, indent=2))