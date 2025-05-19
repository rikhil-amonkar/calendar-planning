import json
from datetime import datetime, timedelta

# Define travel distances in minutes
travel_distances = {
    ('Bayview', 'North Beach'): 21,
    ('Bayview', 'Presidio'): 31,
    ('Bayview', 'Haight-Ashbury'): 19,
    ('Bayview', 'Union Square'): 17,
    ('North Beach', 'Bayview'): 22,
    ('North Beach', 'Presidio'): 17,
    ('North Beach', 'Haight-Ashbury'): 18,
    ('North Beach', 'Union Square'): 7,
    ('Presidio', 'Bayview'): 31,
    ('Presidio', 'North Beach'): 18,
    ('Presidio', 'Haight-Ashbury'): 15,
    ('Presidio', 'Union Square'): 22,
    ('Haight-Ashbury', 'Bayview'): 18,
    ('Haight-Ashbury', 'North Beach'): 19,
    ('Haight-Ashbury', 'Presidio'): 15,
    ('Haight-Ashbury', 'Union Square'): 17,
    ('Union Square', 'Bayview'): 15,
    ('Union Square', 'North Beach'): 10,
    ('Union Square', 'Presidio'): 24,
    ('Union Square', 'Haight-Ashbury'): 18
}

# Define meeting constraints
meetings = [
    {'person': 'Barbara', 'location': 'North Beach','start_time': '13:45', 'end_time': '20:15','min_duration': 60},
    {'person': 'Margaret', 'location': 'Presidio','start_time': '10:15', 'end_time': '15:15','min_duration': 30},
    {'person': 'Kevin', 'location': 'Haight-Ashbury','start_time': '20:00', 'end_time': '20:45','min_duration': 30},
    {'person': 'Kimberly', 'location': 'Union Square','start_time': '07:45', 'end_time': '16:45','min_duration': 30}
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