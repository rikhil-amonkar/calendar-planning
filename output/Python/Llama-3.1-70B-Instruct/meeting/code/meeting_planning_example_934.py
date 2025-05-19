import json
from datetime import datetime, timedelta

# Define travel distances in minutes
travel_distances = {
    ('Nob Hill', 'Embarcadero'): 9,
    ('Nob Hill', 'The Castro'): 17,
    ('Nob Hill', 'Haight-Ashbury'): 13,
    ('Nob Hill', 'Union Square'): 7,
    ('Nob Hill', 'North Beach'): 8,
    ('Nob Hill', 'Pacific Heights'): 8,
    ('Nob Hill', 'Chinatown'): 6,
    ('Nob Hill', 'Golden Gate Park'): 17,
    ('Nob Hill', 'Marina District'): 11,
    ('Nob Hill', 'Russian Hill'): 5,
    ('Embarcadero', 'Nob Hill'): 10,
    ('Embarcadero', 'The Castro'): 25,
    ('Embarcadero', 'Haight-Ashbury'): 21,
    ('Embarcadero', 'Union Square'): 10,
    ('Embarcadero', 'North Beach'): 5,
    ('Embarcadero', 'Pacific Heights'): 11,
    ('Embarcadero', 'Chinatown'): 7,
    ('Embarcadero', 'Golden Gate Park'): 25,
    ('Embarcadero', 'Marina District'): 12,
    ('Embarcadero', 'Russian Hill'): 8,
    ('The Castro', 'Nob Hill'): 16,
    ('The Castro', 'Embarcadero'): 22,
    ('The Castro', 'Haight-Ashbury'): 6,
    ('The Castro', 'Union Square'): 19,
    ('The Castro', 'North Beach'): 20,
    ('The Castro', 'Pacific Heights'): 16,
    ('The Castro', 'Chinatown'): 22,
    ('The Castro', 'Golden Gate Park'): 11,
    ('The Castro', 'Marina District'): 21,
    ('The Castro', 'Russian Hill'): 18,
    ('Haight-Ashbury', 'Nob Hill'): 15,
    ('Haight-Ashbury', 'Embarcadero'): 20,
    ('Haight-Ashbury', 'The Castro'): 6,
    ('Haight-Ashbury', 'Union Square'): 19,
    ('Haight-Ashbury', 'North Beach'): 19,
    ('Haight-Ashbury', 'Pacific Heights'): 12,
    ('Haight-Ashbury', 'Chinatown'): 19,
    ('Haight-Ashbury', 'Golden Gate Park'): 7,
    ('Haight-Ashbury', 'Marina District'): 17,
    ('Haight-Ashbury', 'Russian Hill'): 17,
    ('Union Square', 'Nob Hill'): 9,
    ('Union Square', 'Embarcadero'): 11,
    ('Union Square', 'The Castro'): 17,
    ('Union Square', 'Haight-Ashbury'): 18,
    ('Union Square', 'North Beach'): 10,
    ('Union Square', 'Pacific Heights'): 15,
    ('Union Square', 'Chinatown'): 7,
    ('Union Square', 'Golden Gate Park'): 22,
    ('Union Square', 'Marina District'): 18,
    ('Union Square', 'Russian Hill'): 13,
    ('North Beach', 'Nob Hill'): 7,
    ('North Beach', 'Embarcadero'): 6,
    ('North Beach', 'The Castro'): 23,
    ('North Beach', 'Haight-Ashbury'): 18,
    ('North Beach', 'Union Square'): 7,
    ('North Beach', 'Pacific Heights'): 8,
    ('North Beach', 'Chinatown'): 6,
    ('North Beach', 'Golden Gate Park'): 22,
    ('North Beach', 'Marina District'): 9,
    ('North Beach', 'Russian Hill'): 4,
    ('Pacific Heights', 'Nob Hill'): 8,
    ('Pacific Heights', 'Embarcadero'): 10,
    ('Pacific Heights', 'The Castro'): 16,
    ('Pacific Heights', 'Haight-Ashbury'): 11,
    ('Pacific Heights', 'Union Square'): 12,
    ('Pacific Heights', 'North Beach'): 9,
    ('Pacific Heights', 'Chinatown'): 11,
    ('Pacific Heights', 'Golden Gate Park'): 15,
    ('Pacific Heights', 'Marina District'): 6,
    ('Pacific Heights', 'Russian Hill'): 7,
    ('Chinatown', 'Nob Hill'): 9,
    ('Chinatown', 'Embarcadero'): 5,
    ('Chinatown', 'The Castro'): 22,
    ('Chinatown', 'Haight-Ashbury'): 19,
    ('Chinatown', 'Union Square'): 7,
    ('Chinatown', 'North Beach'): 3,
    ('Chinatown', 'Pacific Heights'): 10,
    ('Chinatown', 'Golden Gate Park'): 23,
    ('Chinatown', 'Marina District'): 12,
    ('Chinatown', 'Russian Hill'): 7,
    ('Golden Gate Park', 'Nob Hill'): 20,
    ('Golden Gate Park', 'Embarcadero'): 25,
    ('Golden Gate Park', 'The Castro'): 13,
    ('Golden Gate Park', 'Haight-Ashbury'): 7,
    ('Golden Gate Park', 'Union Square'): 22,
    ('Golden Gate Park', 'North Beach'): 23,
    ('Golden Gate Park', 'Pacific Heights'): 16,
    ('Golden Gate Park', 'Chinatown'): 23,
    ('Golden Gate Park', 'Marina District'): 16,
    ('Golden Gate Park', 'Russian Hill'): 19,
    ('Marina District', 'Nob Hill'): 12,
    ('Marina District', 'Embarcadero'): 14,
    ('Marina District', 'The Castro'): 22,
    ('Marina District', 'Haight-Ashbury'): 16,
    ('Marina District', 'Union Square'): 16,
    ('Marina District', 'North Beach'): 11,
    ('Marina District', 'Pacific Heights'): 7,
    ('Marina District', 'Chinatown'): 15,
    ('Marina District', 'Golden Gate Park'): 18,
    ('Marina District', 'Russian Hill'): 8,
    ('Russian Hill', 'Nob Hill'): 5,
    ('Russian Hill', 'Embarcadero'): 8,
    ('Russian Hill', 'The Castro'): 21,
    ('Russian Hill', 'Haight-Ashbury'): 17,
    ('Russian Hill', 'Union Square'): 10,
    ('Russian Hill', 'North Beach'): 5,
    ('Russian Hill', 'Pacific Heights'): 7,
    ('Russian Hill', 'Chinatown'): 9,
    ('Russian Hill', 'Golden Gate Park'): 21,
    ('Russian Hill', 'Marina District'): 7
}

# Define meeting constraints
meetings = [
    {'person': 'Mary', 'location': 'Embarcadero','start_time': '20:00', 'end_time': '21:15','min_duration': 75},
    {'person': 'Kenneth', 'location': 'The Castro','start_time': '11:15', 'end_time': '19:15','min_duration': 30},
    {'person': 'Joseph', 'location': 'Haight-Ashbury','start_time': '20:00', 'end_time': '22:00','min_duration': 120},
    {'person': 'Sarah', 'location': 'Union Square','start_time': '11:45', 'end_time': '14:30','min_duration': 90},
    {'person': 'Thomas', 'location': 'North Beach','start_time': '19:15', 'end_time': '19:45','min_duration': 15},
    {'person': 'Daniel', 'location': 'Pacific Heights','start_time': '13:45', 'end_time': '20:30','min_duration': 15},
    {'person': 'Richard', 'location': 'Chinatown','start_time': '08:00', 'end_time': '18:45','min_duration': 30},
    {'person': 'Mark', 'location': 'Golden Gate Park','start_time': '17:30', 'end_time': '21:30','min_duration': 120},
    {'person': 'David', 'location': 'Marina District','start_time': '20:00', 'end_time': '21:00','min_duration': 60},
    {'person': 'Karen', 'location': 'Russian Hill','start_time': '13:15', 'end_time': '18:30','min_duration': 120}
]

# Define arrival time
arrival_time = '09:00'

# Define current location and time
current_location = 'Nob Hill'
current_time = datetime.strptime(arrival_time, '%H:%M')

# Initialize itinerary
itinerary = []

# Function to calculate end time
def calculate_end_time(start_time, duration):
    return (datetime.strptime(start_time, '%H:%M') + timedelta(minutes=duration)).strftime('%H:%M')

# Function to check if meeting can be scheduled
def can_schedule_meeting(meeting):
    global current_time
    global current_location
    travel_time = travel_distances.get((current_location, meeting['location']), float('inf'))
    meeting_start_time = datetime.strptime(meeting['start_time'], '%H:%M')
    if current_time + timedelta(minutes=travel_time) <= meeting_start_time:
        return True
    return False

# Function to schedule meeting
def schedule_meeting(meeting):
    global current_time
    global current_location
    global itinerary
    travel_time = travel_distances.get((current_location, meeting['location']), float('inf'))
    current_time += timedelta(minutes=travel_time)
    current_location = meeting['location']
    meeting_end_time = calculate_end_time(meeting['start_time'], meeting['min_duration'])
    itinerary.append({
        'action':'meet',
        'location': meeting['location'],
        'person': meeting['person'],
     'start_time': meeting['start_time'],
        'end_time': meeting_end_time
    })
    current_time = datetime.strptime(meeting_end_time, '%H:%M')

# Sort meetings by start time
meetings.sort(key=lambda x: x['start_time'])

# Schedule meetings
for meeting in meetings:
    if can_schedule_meeting(meeting):
        schedule_meeting(meeting)

# Print itinerary as JSON
print('SOLUTION:')
print(json.dumps({'itinerary': itinerary}, indent=4))