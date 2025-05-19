import json
from datetime import datetime, timedelta

# Define travel times between locations
travel_times = {
    'Marina District': {'Bayview': 27, 'Sunset District': 19, 'Richmond District': 11, 'Nob Hill': 12, 'Chinatown': 15, 'Haight-Ashbury': 16, 'North Beach': 11, 'Russian Hill': 8, 'Embarcadero': 14},
    'Bayview': {'Marina District': 27, 'Sunset District': 23, 'Richmond District': 25, 'Nob Hill': 20, 'Chinatown': 19, 'Haight-Ashbury': 19, 'North Beach': 22, 'Russian Hill': 23, 'Embarcadero': 19},
    'Sunset District': {'Marina District': 21, 'Bayview': 22, 'Richmond District': 12, 'Nob Hill': 27, 'Chinatown': 30, 'Haight-Ashbury': 15, 'North Beach': 28, 'Russian Hill': 24, 'Embarcadero': 30},
    'Richmond District': {'Marina District': 9, 'Bayview': 27, 'Sunset District': 11, 'Nob Hill': 17, 'Chinatown': 20, 'Haight-Ashbury': 10, 'North Beach': 17, 'Russian Hill': 13, 'Embarcadero': 19},
    'Nob Hill': {'Marina District': 11, 'Bayview': 19, 'Sunset District': 24, 'Richmond District': 14, 'Chinatown': 6, 'Haight-Ashbury': 13, 'North Beach': 8, 'Russian Hill': 5, 'Embarcadero': 9},
    'Chinatown': {'Marina District': 12, 'Bayview': 20, 'Sunset District': 29, 'Richmond District': 20, 'Nob Hill': 9, 'Haight-Ashbury': 19, 'North Beach': 3, 'Russian Hill': 7, 'Embarcadero': 5},
    'Haight-Ashbury': {'Marina District': 17, 'Bayview': 18, 'Sunset District': 15, 'Richmond District': 10, 'Nob Hill': 15, 'Chinatown': 19, 'North Beach': 19, 'Russian Hill': 17, 'Embarcadero': 20},
    'North Beach': {'Marina District': 9, 'Bayview': 25, 'Sunset District': 27, 'Richmond District': 18, 'Nob Hill': 7, 'Chinatown': 6, 'Haight-Ashbury': 18, 'Russian Hill': 4, 'Embarcadero': 6},
    'Russian Hill': {'Marina District': 7, 'Bayview': 23, 'Sunset District': 23, 'Richmond District': 14, 'Nob Hill': 5, 'Chinatown': 9, 'Haight-Ashbury': 17, 'North Beach': 5, 'Embarcadero': 8},
    'Embarcadero': {'Marina District': 12, 'Bayview': 21, 'Sunset District': 30, 'Richmond District': 21, 'Nob Hill': 10, 'Chinatown': 7, 'Haight-Ashbury': 21, 'North Beach': 5, 'Russian Hill': 8}
}

# Define meeting constraints
meetings = [
    {'person': 'Charles', 'location': 'Bayview','start_time': '11:30', 'end_time': '14:30','min_time': 45},
    {'person': 'Robert', 'location': 'Sunset District','start_time': '16:45', 'end_time': '21:00','min_time': 30},
    {'person': 'Karen', 'location': 'Richmond District','start_time': '19:15', 'end_time': '21:30','min_time': 60},
    {'person': 'Rebecca', 'location': 'Nob Hill','start_time': '16:15', 'end_time': '20:30','min_time': 90},
    {'person': 'Margaret', 'location': 'Chinatown','start_time': '14:15', 'end_time': '19:45','min_time': 120},
    {'person': 'Patricia', 'location': 'Haight-Ashbury','start_time': '14:30', 'end_time': '20:30','min_time': 45},
    {'person': 'Mark', 'location': 'North Beach','start_time': '14:00', 'end_time': '18:30','min_time': 105},
    {'person': 'Melissa', 'location': 'Russian Hill','start_time': '13:00', 'end_time': '19:45','min_time': 30},
    {'person': 'Laura', 'location': 'Embarcadero','start_time': '07:45', 'end_time': '13:15','min_time': 105}
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