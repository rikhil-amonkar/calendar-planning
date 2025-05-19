import json
from datetime import datetime, timedelta

# Define travel times between locations
travel_times = {
    'Bayview': {'Embarcadero': 19, 'Fisherman\'s Wharf': 25, 'Financial District': 19},
    'Embarcadero': {'Bayview': 21, 'Fisherman\'s Wharf': 6, 'Financial District': 5},
    'Fisherman\'s Wharf': {'Bayview': 26, 'Embarcadero': 8, 'Financial District': 11},
    'Financial District': {'Bayview': 19, 'Embarcadero': 4, 'Fisherman\'s Wharf': 10}
}

# Define meeting constraints
meetings = [
    {'person': 'Betty', 'location': 'Embarcadero','start_time': '19:45', 'end_time': '21:45','min_time': 15},
    {'person': 'Karen', 'location': 'Fisherman\'s Wharf','start_time': '08:45', 'end_time': '15:00','min_time': 30},
    {'person': 'Anthony', 'location': 'Financial District','start_time': '09:15', 'end_time': '21:30','min_time': 105}
]

def calculate_meeting_schedule(meetings, travel_times):
    schedule = []
    current_time = datetime.strptime('09:00', '%H:%M')
    current_location = 'Bayview'

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