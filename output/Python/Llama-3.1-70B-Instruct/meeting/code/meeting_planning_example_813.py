import json
from datetime import datetime, timedelta

# Define travel times between locations
travel_times = {
    'Marina District': {'Embarcadero': 14, 'Bayview': 27, 'Union Square': 16, 'Chinatown': 15, 'Sunset District': 19, 'Golden Gate Park': 18, 'Financial District': 17, 'Haight-Ashbury': 16, 'Mission District': 20},
    'Embarcadero': {'Marina District': 12, 'Bayview': 21, 'Union Square': 10, 'Chinatown': 7, 'Sunset District': 30, 'Golden Gate Park': 25, 'Financial District': 5, 'Haight-Ashbury': 21, 'Mission District': 20},
    'Bayview': {'Marina District': 27, 'Embarcadero': 19, 'Union Square': 18, 'Chinatown': 19, 'Sunset District': 23, 'Golden Gate Park': 22, 'Financial District': 19, 'Haight-Ashbury': 19, 'Mission District': 13},
    'Union Square': {'Marina District': 18, 'Embarcadero': 11, 'Bayview': 15, 'Chinatown': 7, 'Sunset District': 27, 'Golden Gate Park': 22, 'Financial District': 9, 'Haight-Ashbury': 18, 'Mission District': 14},
    'Chinatown': {'Marina District': 12, 'Embarcadero': 5, 'Bayview': 20, 'Union Square': 7, 'Sunset District': 29, 'Golden Gate Park': 23, 'Financial District': 5, 'Haight-Ashbury': 19, 'Mission District': 17},
    'Sunset District': {'Marina District': 21, 'Embarcadero': 30, 'Bayview': 22, 'Union Square': 30, 'Chinatown': 30, 'Golden Gate Park': 11, 'Financial District': 30, 'Haight-Ashbury': 15, 'Mission District': 25},
    'Golden Gate Park': {'Marina District': 16, 'Embarcadero': 25, 'Bayview': 23, 'Union Square': 22, 'Chinatown': 23, 'Sunset District': 10, 'Financial District': 26, 'Haight-Ashbury': 7, 'Mission District': 17},
    'Financial District': {'Marina District': 15, 'Embarcadero': 4, 'Bayview': 19, 'Union Square': 9, 'Chinatown': 5, 'Sunset District': 30, 'Golden Gate Park': 23, 'Haight-Ashbury': 19, 'Mission District': 17},
    'Haight-Ashbury': {'Marina District': 17, 'Embarcadero': 20, 'Bayview': 18, 'Union Square': 19, 'Chinatown': 19, 'Sunset District': 15, 'Golden Gate Park': 7, 'Financial District': 21, 'Mission District': 11},
    'Mission District': {'Marina District': 19, 'Embarcadero': 19, 'Bayview': 14, 'Union Square': 15, 'Chinatown': 16, 'Sunset District': 24, 'Golden Gate Park': 17, 'Financial District': 15, 'Haight-Ashbury': 12}
}

# Define meeting constraints
meetings = [
    {'person': 'Joshua', 'location': 'Embarcadero','start_time': '09:45', 'end_time': '18:00','min_time': 105},
    {'person': 'Jeffrey', 'location': 'Bayview','start_time': '09:45', 'end_time': '20:15','min_time': 75},
    {'person': 'Charles', 'location': 'Union Square','start_time': '10:45', 'end_time': '20:15','min_time': 120},
    {'person': 'Joseph', 'location': 'Chinatown','start_time': '07:00', 'end_time': '15:30','min_time': 60},
    {'person': 'Elizabeth', 'location': 'Sunset District','start_time': '09:00', 'end_time': '09:45','min_time': 45},
    {'person': 'Matthew', 'location': 'Golden Gate Park','start_time': '11:00', 'end_time': '19:30','min_time': 45},
    {'person': 'Carol', 'location': 'Financial District','start_time': '10:45', 'end_time': '11:15','min_time': 15},
    {'person': 'Paul', 'location': 'Haight-Ashbury','start_time': '19:15', 'end_time': '20:30','min_time': 15},
    {'person': 'Rebecca', 'location': 'Mission District','start_time': '17:00', 'end_time': '21:45','min_time': 45}
]

def calculate_meeting_schedule(meetings, travel_times):
    schedule = []
    current_time = datetime.strptime('09:00', '%H:%M')
    current_location = 'Marina District'

    for meeting in meetings:
        # Calculate travel time to meeting location
        travel_time = travel_times[current_location][meeting['location']]
        arrival_time = current_time + timedelta(minutes=travel_time)

        # Check if meeting can be attended
        meeting_start_time = datetime.strptime(meeting['start_time'], '%H:%M')
        meeting_end_time = datetime.strptime(meeting['end_time'], '%H:%M')
        if arrival_time < meeting_end_time and arrival_time + timedelta(minutes=meeting['min_time']) <= meeting_end_time:
            # Attend meeting
            meeting_end = min(arrival_time + timedelta(minutes=meeting['min_time']), meeting_end_time)
            schedule.append({
                'action':'meet',
                'location': meeting['location'],
                'person': meeting['person'],
            'start_time': arrival_time.strftime('%H:%M'),
                'end_time': meeting_end.strftime('%H:%M')
            })
            current_time = meeting_end
            current_location = meeting['location']
        else:
            # Skip meeting
            continue

    return schedule

# Calculate and print meeting schedule
schedule = calculate_meeting_schedule(meetings, travel_times)
print(json.dumps({'itinerary': schedule}, indent=4))