import json
from datetime import datetime, timedelta

# Define travel times between locations
travel_times = {
    'Embarcadero': {'Presidio': 20, 'Richmond District': 21, 'Fisherman\'s Wharf': 6},
    'Presidio': {'Embarcadero': 20, 'Richmond District': 7, 'Fisherman\'s Wharf': 19},
    'Richmond District': {'Embarcadero': 19, 'Presidio': 7, 'Fisherman\'s Wharf': 18},
    'Fisherman\'s Wharf': {'Embarcadero': 8, 'Presidio': 17, 'Richmond District': 18}
}

# Define meeting constraints
meetings = [
    {'person': 'Betty', 'location': 'Presidio','start_time': '10:15', 'end_time': '21:30','min_time': 45},
    {'person': 'David', 'location': 'Richmond District','start_time': '13:00', 'end_time': '20:15','min_time': 90},
    {'person': 'Barbara', 'location': 'Fisherman\'s Wharf','start_time': '09:15', 'end_time': '20:15','min_time': 120}
]

def calculate_meeting_schedule(meetings, travel_times):
    schedule = []
    current_time = datetime.strptime('09:00', '%H:%M')
    current_location = 'Embarcadero'

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