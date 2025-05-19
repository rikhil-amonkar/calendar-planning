import json
from datetime import datetime, timedelta

# Define travel times between locations
travel_times = {
    'Richmond District': {'Sunset District': 11, 'Haight-Ashbury': 10, 'Mission District': 20, 'Golden Gate Park': 9},
    'Sunset District': {'Richmond District': 12, 'Haight-Ashbury': 15, 'Mission District': 24, 'Golden Gate Park': 11},
    'Haight-Ashbury': {'Richmond District': 10, 'Sunset District': 15, 'Mission District': 11, 'Golden Gate Park': 7},
    'Mission District': {'Richmond District': 20, 'Sunset District': 24, 'Haight-Ashbury': 12, 'Golden Gate Park': 17},
    'Golden Gate Park': {'Richmond District': 7, 'Sunset District': 10, 'Haight-Ashbury': 7, 'Mission District': 17}
}

# Define meeting constraints
meetings = [
    {'person': 'Sarah', 'location': 'Sunset District','start_time': '10:45', 'end_time': '19:00','min_time': 30},
    {'person': 'Richard', 'location': 'Haight-Ashbury','start_time': '11:45', 'end_time': '15:45','min_time': 90},
    {'person': 'Elizabeth', 'location': 'Mission District','start_time': '11:00', 'end_time': '17:15','min_time': 120},
    {'person': 'Michelle', 'location': 'Golden Gate Park','start_time': '18:15', 'end_time': '20:45','min_time': 90}
]

def calculate_meeting_schedule(meetings, travel_times):
    schedule = []
    current_time = datetime.strptime('09:00', '%H:%M')
    current_location = 'Richmond District'

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