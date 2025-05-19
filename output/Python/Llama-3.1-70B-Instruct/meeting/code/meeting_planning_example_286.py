import json
from datetime import datetime, timedelta

# Define travel distances in minutes
travel_distances = {
    ('Union Square', 'Mission District'): 14,
    ('Union Square', 'Bayview'): 15,
    ('Union Square', 'Sunset District'): 26,
    ('Mission District', 'Union Square'): 15,
    ('Mission District', 'Bayview'): 15,
    ('Mission District', 'Sunset District'): 24,
    ('Bayview', 'Union Square'): 17,
    ('Bayview', 'Mission District'): 13,
    ('Bayview', 'Sunset District'): 23,
    ('Sunset District', 'Union Square'): 30,
    ('Sunset District', 'Mission District'): 24,
    ('Sunset District', 'Bayview'): 22
}

# Define meeting constraints
meetings = [
    {'person': 'Rebecca', 'location': 'Mission District','start_time': '11:30', 'end_time': '20:15','min_duration': 120},
    {'person': 'Karen', 'location': 'Bayview','start_time': '12:45', 'end_time': '15:00','min_duration': 120},
    {'person': 'Carol', 'location': 'Sunset District','start_time': '10:15', 'end_time': '11:45','min_duration': 30}
]

# Define arrival time
arrival_time = '09:00'

# Define current location and time
current_location = 'Union Square'
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