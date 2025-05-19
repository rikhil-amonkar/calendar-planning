import json
from datetime import datetime, timedelta

# Define travel times between locations
travel_times = {
    'North Beach': {'Union Square': 7, 'Russian Hill': 4},
    'Union Square': {'North Beach': 10, 'Russian Hill': 13},
    'Russian Hill': {'North Beach': 5, 'Union Square': 11}
}

# Define meeting constraints
meetings = [
    {'person': 'Emily', 'location': 'Union Square','start_time': '16:00', 'end_time': '17:15','min_time': 45},
    {'person': 'Margaret', 'location': 'Russian Hill','start_time': '19:00', 'end_time': '21:00','min_time': 120}
]

def calculate_meeting_schedule(meetings, travel_times):
    schedule = []
    current_time = datetime.strptime('09:00', '%H:%M')
    current_location = 'North Beach'

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