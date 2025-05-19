import json
from datetime import datetime, timedelta

# Define travel distances in minutes
travel_distances = {
    ('Embarcadero', 'Fisherman\'s Wharf'): 6,
    ('Embarcadero', 'Financial District'): 5,
    ('Embarcadero', 'Russian Hill'): 8,
    ('Embarcadero', 'Marina District'): 12,
    ('Embarcadero', 'Richmond District'): 21,
    ('Embarcadero', 'Pacific Heights'): 11,
    ('Embarcadero', 'Haight-Ashbury'): 21,
    ('Embarcadero', 'Presidio'): 20,
    ('Embarcadero', 'Nob Hill'): 10,
    ('Embarcadero', 'The Castro'): 25,
    ('Fisherman\'s Wharf', 'Embarcadero'): 8,
    ('Fisherman\'s Wharf', 'Financial District'): 11,
    ('Fisherman\'s Wharf', 'Russian Hill'): 7,
    ('Fisherman\'s Wharf', 'Marina District'): 9,
    ('Fisherman\'s Wharf', 'Richmond District'): 18,
    ('Fisherman\'s Wharf', 'Pacific Heights'): 12,
    ('Fisherman\'s Wharf', 'Haight-Ashbury'): 22,
    ('Fisherman\'s Wharf', 'Presidio'): 17,
    ('Fisherman\'s Wharf', 'Nob Hill'): 11,
    ('Fisherman\'s Wharf', 'The Castro'): 27,
    ('Financial District', 'Embarcadero'): 4,
    ('Financial District', 'Fisherman\'s Wharf'): 10,
    ('Financial District', 'Russian Hill'): 11,
    ('Financial District', 'Marina District'): 15,
    ('Financial District', 'Richmond District'): 21,
    ('Financial District', 'Pacific Heights'): 13,
    ('Financial District', 'Haight-Ashbury'): 19,
    ('Financial District', 'Presidio'): 22,
    ('Financial District', 'Nob Hill'): 8,
    ('Financial District', 'The Castro'): 20,
    ('Russian Hill', 'Embarcadero'): 8,
    ('Russian Hill', 'Fisherman\'s Wharf'): 7,
    ('Russian Hill', 'Financial District'): 11,
    ('Russian Hill', 'Marina District'): 7,
    ('Russian Hill', 'Richmond District'): 14,
    ('Russian Hill', 'Pacific Heights'): 7,
    ('Russian Hill', 'Haight-Ashbury'): 17,
    ('Russian Hill', 'Presidio'): 14,
    ('Russian Hill', 'Nob Hill'): 5,
    ('Russian Hill', 'The Castro'): 21,
    ('Marina District', 'Embarcadero'): 14,
    ('Marina District', 'Fisherman\'s Wharf'): 10,
    ('Marina District', 'Financial District'): 17,
    ('Marina District', 'Russian Hill'): 8,
    ('Marina District', 'Richmond District'): 11,
    ('Marina District', 'Pacific Heights'): 7,
    ('Marina District', 'Haight-Ashbury'): 16,
    ('Marina District', 'Presidio'): 10,
    ('Marina District', 'Nob Hill'): 12,
    ('Marina District', 'The Castro'): 22,
    ('Richmond District', 'Embarcadero'): 19,
    ('Richmond District', 'Fisherman\'s Wharf'): 18,
    ('Richmond District', 'Financial District'): 22,
    ('Richmond District', 'Russian Hill'): 13,
    ('Richmond District', 'Marina District'): 9,
    ('Richmond District', 'Pacific Heights'): 10,
    ('Richmond District', 'Haight-Ashbury'): 10,
    ('Richmond District', 'Presidio'): 7,
    ('Richmond District', 'Nob Hill'): 17,
    ('Richmond District', 'The Castro'): 16,
    ('Pacific Heights', 'Embarcadero'): 10,
    ('Pacific Heights', 'Fisherman\'s Wharf'): 13,
    ('Pacific Heights', 'Financial District'): 13,
    ('Pacific Heights', 'Russian Hill'): 7,
    ('Pacific Heights', 'Marina District'): 6,
    ('Pacific Heights', 'Richmond District'): 12,
    ('Pacific Heights', 'Haight-Ashbury'): 11,
    ('Pacific Heights', 'Presidio'): 11,
    ('Pacific Heights', 'Nob Hill'): 8,
    ('Pacific Heights', 'The Castro'): 16,
    ('Haight-Ashbury', 'Embarcadero'): 20,
    ('Haight-Ashbury', 'Fisherman\'s Wharf'): 23,
    ('Haight-Ashbury', 'Financial District'): 21,
    ('Haight-Ashbury', 'Russian Hill'): 17,
    ('Haight-Ashbury', 'Marina District'): 17,
    ('Haight-Ashbury', 'Richmond District'): 10,
    ('Haight-Ashbury', 'Pacific Heights'): 12,
    ('Haight-Ashbury', 'Presidio'): 15,
    ('Haight-Ashbury', 'Nob Hill'): 15,
    ('Haight-Ashbury', 'The Castro'): 6,
    ('Presidio', 'Embarcadero'): 20,
    ('Presidio', 'Fisherman\'s Wharf'): 19,
    ('Presidio', 'Financial District'): 23,
    ('Presidio', 'Russian Hill'): 14,
    ('Presidio', 'Marina District'): 11,
    ('Presidio', 'Richmond District'): 7,
    ('Presidio', 'Pacific Heights'): 11,
    ('Presidio', 'Haight-Ashbury'): 15,
    ('Presidio', 'Nob Hill'): 18,
    ('Presidio', 'The Castro'): 21,
    ('Nob Hill', 'Embarcadero'): 9,
    ('Nob Hill', 'Fisherman\'s Wharf'): 10,
    ('Nob Hill', 'Financial District'): 9,
    ('Nob Hill', 'Russian Hill'): 5,
    ('Nob Hill', 'Marina District'): 11,
    ('Nob Hill', 'Richmond District'): 14,
    ('Nob Hill', 'Pacific Heights'): 8,
    ('Nob Hill', 'Haight-Ashbury'): 13,
    ('Nob Hill', 'Presidio'): 17,
    ('Nob Hill', 'The Castro'): 17,
    ('The Castro', 'Embarcadero'): 22,
    ('The Castro', 'Fisherman\'s Wharf'): 24,
    ('The Castro', 'Financial District'): 21,
    ('The Castro', 'Russian Hill'): 18,
    ('The Castro', 'Marina District'): 21,
    ('The Castro', 'Richmond District'): 16,
    ('The Castro', 'Pacific Heights'): 16,
    ('The Castro', 'Haight-Ashbury'): 6,
    ('The Castro', 'Presidio'): 20,
    ('The Castro', 'Nob Hill'): 16
}

# Define meeting constraints
meetings = [
    {'person': 'Stephanie', 'location': 'Fisherman\'s Wharf','start_time': '15:30', 'end_time': '22:00','min_duration': 30},
    {'person': 'Lisa', 'location': 'Financial District','start_time': '10:45', 'end_time': '17:15','min_duration': 15},
    {'person': 'Melissa', 'location': 'Russian Hill','start_time': '17:00', 'end_time': '21:45','min_duration': 120},
    {'person': 'Betty', 'location': 'Marina District','start_time': '10:45', 'end_time': '14:15','min_duration': 60},
    {'person': 'Sarah', 'location': 'Richmond District','start_time': '16:15', 'end_time': '19:30','min_duration': 105},
    {'person': 'Daniel', 'location': 'Pacific Heights','start_time': '18:30', 'end_time': '21:45','min_duration': 60},
    {'person': 'Joshua', 'location': 'Haight-Ashbury','start_time': '09:00', 'end_time': '15:30','min_duration': 15},
    {'person': 'Joseph', 'location': 'Presidio','start_time': '07:00', 'end_time': '13:00','min_duration': 45},
    {'person': 'Andrew', 'location': 'Nob Hill','start_time': '19:45', 'end_time': '22:00','min_duration': 105},
    {'person': 'John', 'location': 'The Castro','start_time': '13:15', 'end_time': '19:45','min_duration': 45}
]

# Define arrival time
arrival_time = '09:00'

# Define current location and time
current_location = 'Embarcadero'
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