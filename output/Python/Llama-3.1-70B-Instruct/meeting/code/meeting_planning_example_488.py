import json
from datetime import datetime, timedelta

# Define travel times between locations
travel_times = {
    'Pacific Heights': {'Nob Hill': 8, 'Russian Hill': 7, 'The Castro': 16, 'Sunset District': 21, 'Haight-Ashbury': 11},
    'Nob Hill': {'Pacific Heights': 8, 'Russian Hill': 5, 'The Castro': 17, 'Sunset District': 25, 'Haight-Ashbury': 13},
    'Russian Hill': {'Pacific Heights': 7, 'Nob Hill': 5, 'The Castro': 21, 'Sunset District': 23, 'Haight-Ashbury': 17},
    'The Castro': {'Pacific Heights': 16, 'Nob Hill': 16, 'Russian Hill': 18, 'Sunset District': 17, 'Haight-Ashbury': 6},
    'Sunset District': {'Pacific Heights': 21, 'Nob Hill': 27, 'Russian Hill': 24, 'The Castro': 17, 'Haight-Ashbury': 15},
    'Haight-Ashbury': {'Pacific Heights': 12, 'Nob Hill': 15, 'Russian Hill': 17, 'The Castro': 6, 'Sunset District': 15}
}

# Define meeting constraints
meetings = [
    {'person': 'Ronald', 'location': 'Nob Hill','start_time': '10:00', 'end_time': '17:00','min_time': 105},
    {'person': 'Sarah', 'location': 'Russian Hill','start_time': '07:15', 'end_time': '09:30','min_time': 45},
    {'person': 'Helen', 'location': 'The Castro','start_time': '13:30', 'end_time': '17:00','min_time': 120},
    {'person': 'Joshua', 'location': 'Sunset District','start_time': '14:15', 'end_time': '19:30','min_time': 90},
    {'person': 'Margaret', 'location': 'Haight-Ashbury','start_time': '10:15', 'end_time': '22:00','min_time': 60}
]

def calculate_meeting_schedule(meetings, travel_times):
    schedule = []
    current_time = datetime.strptime('09:00', '%H:%M')
    current_location = 'Pacific Heights'

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