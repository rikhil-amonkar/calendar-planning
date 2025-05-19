import json
from datetime import datetime, timedelta

# Define travel distances in minutes
travel_distances = {
    ('Bayview', 'Embarcadero'): 19,
    ('Bayview', 'Richmond District'): 25,
    ('Bayview', 'Fisherman\'s Wharf'): 25,
    ('Embarcadero', 'Bayview'): 21,
    ('Embarcadero', 'Richmond District'): 21,
    ('Embarcadero', 'Fisherman\'s Wharf'): 6,
    ('Richmond District', 'Bayview'): 26,
    ('Richmond District', 'Embarcadero'): 19,
    ('Richmond District', 'Fisherman\'s Wharf'): 18,
    ('Fisherman\'s Wharf', 'Bayview'): 26,
    ('Fisherman\'s Wharf', 'Embarcadero'): 8,
    ('Fisherman\'s Wharf', 'Richmond District'): 18
}

# Define meeting constraints
meetings = [
    {'person': 'Jessica', 'location': 'Embarcadero','start_time': '16:45', 'end_time': '19:00','min_duration': 30},
    {'person': 'Sandra', 'location': 'Richmond District','start_time': '18:30', 'end_time': '21:45','min_duration': 120},
    {'person': 'Jason', 'location': 'Fisherman\'s Wharf','start_time': '16:00', 'end_time': '16:45','min_duration': 30}
]

# Define arrival time
arrival_time = '09:00'

# Define current location and time
current_location = 'Bayview'
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