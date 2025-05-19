import json
from datetime import datetime, timedelta

# Define travel times between locations
travel_times = {
    'Nob Hill': {'Richmond District': 14, 'Financial District': 9, 'North Beach': 8, 'The Castro': 17, 'Golden Gate Park': 17},
    'Richmond District': {'Nob Hill': 17, 'Financial District': 22, 'North Beach': 17, 'The Castro': 16, 'Golden Gate Park': 9},
    'Financial District': {'Nob Hill': 8, 'Richmond District': 21, 'North Beach': 7, 'The Castro': 23, 'Golden Gate Park': 23},
    'North Beach': {'Nob Hill': 7, 'Richmond District': 18, 'Financial District': 8, 'The Castro': 22, 'Golden Gate Park': 22},
    'The Castro': {'Nob Hill': 16, 'Richmond District': 16, 'Financial District': 20, 'North Beach': 20, 'Golden Gate Park': 11},
    'Golden Gate Park': {'Nob Hill': 20, 'Richmond District': 7, 'Financial District': 26, 'North Beach': 24, 'The Castro': 13}
}

# Define meeting constraints
meetings = [
    {'person': 'Emily', 'location': 'Richmond District','start_time': '19:00', 'end_time': '21:00','min_time': 15},
    {'person': 'Margaret', 'location': 'Financial District','start_time': '16:30', 'end_time': '20:15','min_time': 75},
    {'person': 'Ronald', 'location': 'North Beach','start_time': '18:30', 'end_time': '19:30','min_time': 45},
    {'person': 'Deborah', 'location': 'The Castro','start_time': '13:45', 'end_time': '21:15','min_time': 90},
    {'person': 'Jeffrey', 'location': 'Golden Gate Park','start_time': '11:15', 'end_time': '14:30','min_time': 120}
]

def calculate_meeting_schedule(meetings, travel_times):
    schedule = []
    current_time = datetime.strptime('09:00', '%H:%M')
    current_location = 'Nob Hill'

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