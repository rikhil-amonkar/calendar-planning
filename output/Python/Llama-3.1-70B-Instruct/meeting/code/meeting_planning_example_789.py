import json
from datetime import datetime, timedelta

# Define travel times between locations
travel_times = {
    'Union Square': {'Russian Hill': 13, 'Alamo Square': 15, 'Haight-Ashbury': 18, 'Marina District': 18, 'Bayview': 15, 'Chinatown': 7, 'Presidio': 24, 'Sunset District': 27},
    'Russian Hill': {'Union Square': 10, 'Alamo Square': 15, 'Haight-Ashbury': 17, 'Marina District': 7, 'Bayview': 23, 'Chinatown': 9, 'Presidio': 14, 'Sunset District': 23},
    'Alamo Square': {'Union Square': 14, 'Russian Hill': 13, 'Haight-Ashbury': 5, 'Marina District': 15, 'Bayview': 16, 'Chinatown': 15, 'Presidio': 17, 'Sunset District': 16},
    'Haight-Ashbury': {'Union Square': 19, 'Russian Hill': 17, 'Alamo Square': 5, 'Marina District': 17, 'Bayview': 18, 'Chinatown': 19, 'Presidio': 15, 'Sunset District': 15},
    'Marina District': {'Union Square': 16, 'Russian Hill': 8, 'Alamo Square': 15, 'Haight-Ashbury': 16, 'Bayview': 27, 'Chinatown': 15, 'Presidio': 10, 'Sunset District': 19},
    'Bayview': {'Union Square': 18, 'Russian Hill': 23, 'Alamo Square': 16, 'Haight-Ashbury': 19, 'Marina District': 27, 'Chinatown': 19, 'Presidio': 32, 'Sunset District': 23},
    'Chinatown': {'Union Square': 7, 'Russian Hill': 7, 'Alamo Square': 17, 'Haight-Ashbury': 19, 'Marina District': 12, 'Bayview': 20, 'Presidio': 19, 'Sunset District': 29},
    'Presidio': {'Union Square': 22, 'Russian Hill': 14, 'Alamo Square': 19, 'Haight-Ashbury': 15, 'Marina District': 11, 'Bayview': 31, 'Chinatown': 21, 'Sunset District': 15},
    'Sunset District': {'Union Square': 30, 'Russian Hill': 24, 'Alamo Square': 17, 'Haight-Ashbury': 15, 'Marina District': 21, 'Bayview': 22, 'Chinatown': 30, 'Presidio': 16}
}

# Define meeting constraints
meetings = [
    {'person': 'Betty', 'location': 'Russian Hill','start_time': '07:00', 'end_time': '16:45','min_time': 105},
    {'person': 'Melissa', 'location': 'Alamo Square','start_time': '09:30', 'end_time': '17:15','min_time': 105},
    {'person': 'Joshua', 'location': 'Haight-Ashbury','start_time': '12:15', 'end_time': '19:00','min_time': 90},
    {'person': 'Jeffrey', 'location': 'Marina District','start_time': '12:15', 'end_time': '18:00','min_time': 45},
    {'person': 'James', 'location': 'Bayview','start_time': '07:30', 'end_time': '20:00','min_time': 90},
    {'person': 'Anthony', 'location': 'Chinatown','start_time': '11:45', 'end_time': '13:30','min_time': 75},
    {'person': 'Timothy', 'location': 'Presidio','start_time': '12:30', 'end_time': '14:45','min_time': 90},
    {'person': 'Emily', 'location': 'Sunset District','start_time': '19:30', 'end_time': '21:30','min_time': 120}
]

def calculate_meeting_schedule(meetings, travel_times):
    schedule = []
    current_time = datetime.strptime('09:00', '%H:%M')
    current_location = 'Union Square'

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