import json
from datetime import datetime, timedelta

# Travel distances in minutes
travel_times = {
    'Marina District': {
        'Bayview': 27, 'Sunset District': 19, 'Richmond District': 11, 
        'Nob Hill': 12, 'Chinatown': 15, 'Haight-Ashbury': 16, 
        'North Beach': 11, 'Russian Hill': 8, 'Embarcadero': 14
    },
    'Bayview': {
        'Marina District': 27, 'Sunset District': 23, 'Richmond District': 25, 
        'Nob Hill': 20, 'Chinatown': 19, 'Haight-Ashbury': 19, 
        'North Beach': 22, 'Russian Hill': 23, 'Embarcadero': 19
    },
    'Sunset District': {
        'Marina District': 21, 'Bayview': 22, 'Richmond District': 12, 
        'Nob Hill': 27, 'Chinatown': 30, 'Haight-Ashbury': 15, 
        'North Beach': 28, 'Russian Hill': 24, 'Embarcadero': 30
    },
    'Richmond District': {
        'Marina District': 9, 'Bayview': 27, 'Sunset District': 11, 
        'Nob Hill': 17, 'Chinatown': 20, 'Haight-Ashbury': 10, 
        'North Beach': 17, 'Russian Hill': 13, 'Embarcadero': 19
    },
    'Nob Hill': {
        'Marina District': 11, 'Bayview': 19, 'Sunset District': 24, 
        'Richmond District': 14, 'Chinatown': 9, 'Haight-Ashbury': 13, 
        'North Beach': 8, 'Russian Hill': 5, 'Embarcadero': 9
    },
    'Chinatown': {
        'Marina District': 12, 'Bayview': 20, 'Sunset District': 29, 
        'Richmond District': 20, 'Nob Hill': 9, 'Haight-Ashbury': 19, 
        'North Beach': 3, 'Russian Hill': 7, 'Embarcadero': 5
    },
    'Haight-Ashbury': {
        'Marina District': 17, 'Bayview': 18, 'Sunset District': 15, 
        'Richmond District': 10, 'Nob Hill': 15, 'Chinatown': 19, 
        'North Beach': 19, 'Russian Hill': 17, 'Embarcadero': 20
    },
    'North Beach': {
        'Marina District': 9, 'Bayview': 25, 'Sunset District': 27, 
        'Richmond District': 18, 'Nob Hill': 7, 'Chinatown': 6, 
        'Haight-Ashbury': 18, 'Russian Hill': 4, 'Embarcadero': 6
    },
    'Russian Hill': {
        'Marina District': 7, 'Bayview': 23, 'Sunset District': 23, 
        'Richmond District': 14, 'Nob Hill': 5, 'Chinatown': 9, 
        'Haight-Ashbury': 17, 'North Beach': 5, 'Embarcadero': 8
    },
    'Embarcadero': {
        'Marina District': 12, 'Bayview': 21, 'Sunset District': 30, 
        'Richmond District': 21, 'Nob Hill': 10, 'Chinatown': 7, 
        'Haight-Ashbury': 21, 'North Beach': 5, 'Russian Hill': 8
    },
}

# Meeting constraints
meetings = [
    {'name': 'Charles', 'location': 'Bayview', 'start': '11:30', 'end': '14:30', 'minimum_time': 45},
    {'name': 'Robert', 'location': 'Sunset District', 'start': '16:45', 'end': '21:00', 'minimum_time': 30},
    {'name': 'Karen', 'location': 'Richmond District', 'start': '19:15', 'end': '21:30', 'minimum_time': 60},
    {'name': 'Rebecca', 'location': 'Nob Hill', 'start': '16:15', 'end': '20:30', 'minimum_time': 90},
    {'name': 'Margaret', 'location': 'Chinatown', 'start': '14:15', 'end': '19:45', 'minimum_time': 120},
    {'name': 'Patricia', 'location': 'Haight-Ashbury', 'start': '14:30', 'end': '20:30', 'minimum_time': 45},
    {'name': 'Mark', 'location': 'North Beach', 'start': '14:00', 'end': '18:30', 'minimum_time': 105},
    {'name': 'Melissa', 'location': 'Russian Hill', 'start': '13:00', 'end': '19:45', 'minimum_time': 30},
    {'name': 'Laura', 'location': 'Embarcadero', 'start': '7:45', 'end': '13:15', 'minimum_time': 105}
]

# Itinerary
itinerary = []
current_time = datetime.strptime("09:00", "%H:%M")
start_of_day = current_time
visit_location = 'Marina District'

# Function to find meeting schedule
def schedule_meetings(current_time, meetings, itinerary, travel_times):
    for meeting in meetings:
        start_time = datetime.strptime(meeting['start'], "%H:%M")
        end_time = datetime.strptime(meeting['end'], "%H:%M")
        minimum_time = timedelta(minutes=meeting['minimum_time'])
        
        # Travel to meeting location
        travel_time = travel_times[visit_location][meeting['location']]
        arrive_time = current_time + timedelta(minutes=travel_time)

        if arrive_time <= start_time:
            start_meeting_time = start_time
        else:
            start_meeting_time = arrive_time

        if start_meeting_time + minimum_time <= end_time:
            end_meeting_time = start_meeting_time + minimum_time
            itinerary.append({
                'action': 'meet',
                'location': meeting['location'],
                'person': meeting['name'],
                'start_time': start_meeting_time.strftime("%H:%M"),
                'end_time': end_meeting_time.strftime("%H:%M")
            })
            current_time = end_meeting_time

            # Update travel location
            visit_location = meeting['location']
            # Current time after travel time to next meeting
            current_time += timedelta(minutes=travel_time)

# Schedule meetings
schedule_meetings(current_time, meetings, itinerary, travel_times)

# Output the result as JSON
output = {"itinerary": itinerary}
print(json.dumps(output, indent=2))