import json
from datetime import datetime, timedelta

# Define travel times between locations
travel_times = {
    'The Castro': {'North Beach': 20, 'Golden Gate Park': 11, 'Embarcadero': 22, 'Haight-Ashbury': 6, 'Richmond District': 16, 'Nob Hill': 16, 'Marina District': 21, 'Presidio': 20, 'Union Square': 19, 'Financial District': 21},
    'North Beach': {'The Castro': 23, 'Golden Gate Park': 22, 'Embarcadero': 6, 'Haight-Ashbury': 18, 'Richmond District': 18, 'Nob Hill': 7, 'Marina District': 9, 'Presidio': 17, 'Union Square': 7, 'Financial District': 8},
    'Golden Gate Park': {'The Castro': 13, 'North Beach': 23, 'Embarcadero': 25, 'Haight-Ashbury': 7, 'Richmond District': 7, 'Nob Hill': 20, 'Marina District': 16, 'Presidio': 11, 'Union Square': 22, 'Financial District': 26},
    'Embarcadero': {'The Castro': 25, 'North Beach': 5, 'Golden Gate Park': 25, 'Haight-Ashbury': 21, 'Richmond District': 21, 'Nob Hill': 10, 'Marina District': 12, 'Presidio': 20, 'Union Square': 10, 'Financial District': 5},
    'Haight-Ashbury': {'The Castro': 6, 'North Beach': 19, 'Golden Gate Park': 7, 'Embarcadero': 20, 'Richmond District': 10, 'Nob Hill': 15, 'Marina District': 17, 'Presidio': 15, 'Union Square': 19, 'Financial District': 21},
    'Richmond District': {'The Castro': 16, 'North Beach': 17, 'Golden Gate Park': 9, 'Embarcadero': 19, 'Haight-Ashbury': 10, 'Nob Hill': 17, 'Marina District': 9, 'Presidio': 7, 'Union Square': 21, 'Financial District': 22},
    'Nob Hill': {'The Castro': 17, 'North Beach': 8, 'Golden Gate Park': 17, 'Embarcadero': 9, 'Haight-Ashbury': 13, 'Richmond District': 14, 'Marina District': 11, 'Presidio': 17, 'Union Square': 7, 'Financial District': 9},
    'Marina District': {'The Castro': 22, 'North Beach': 11, 'Golden Gate Park': 18, 'Embarcadero': 14, 'Haight-Ashbury': 16, 'Richmond District': 11, 'Nob Hill': 12, 'Presidio': 10, 'Union Square': 16, 'Financial District': 17},
    'Presidio': {'The Castro': 21, 'North Beach': 18, 'Golden Gate Park': 12, 'Embarcadero': 20, 'Haight-Ashbury': 15, 'Richmond District': 7, 'Nob Hill': 18, 'Marina District': 11, 'Union Square': 22, 'Financial District': 23},
    'Union Square': {'The Castro': 17, 'North Beach': 10, 'Golden Gate Park': 22, 'Embarcadero': 11, 'Haight-Ashbury': 18, 'Richmond District': 20, 'Nob Hill': 9, 'Marina District': 18, 'Presidio': 24, 'Financial District': 9},
    'Financial District': {'The Castro': 20, 'North Beach': 7, 'Golden Gate Park': 23, 'Embarcadero': 4, 'Haight-Ashbury': 19, 'Richmond District': 21, 'Nob Hill': 8, 'Marina District': 15, 'Presidio': 22, 'Union Square': 9}
}

# Define meeting constraints
meetings = [
    {'person': 'Steven', 'location': 'North Beach','start_time': '17:30', 'end_time': '20:30','min_time': 15},
    {'person': 'Sarah', 'location': 'Golden Gate Park','start_time': '17:00', 'end_time': '19:15','min_time': 75},
    {'person': 'Brian', 'location': 'Embarcadero','start_time': '14:15', 'end_time': '16:00','min_time': 105},
    {'person': 'Stephanie', 'location': 'Haight-Ashbury','start_time': '10:15', 'end_time': '12:15','min_time': 75},
    {'person': 'Melissa', 'location': 'Richmond District','start_time': '14:00', 'end_time': '19:30','min_time': 30},
    {'person': 'Nancy', 'location': 'Nob Hill','start_time': '08:15', 'end_time': '12:45','min_time': 90},
    {'person': 'David', 'location': 'Marina District','start_time': '11:15', 'end_time': '13:15','min_time': 120},
    {'person': 'James', 'location': 'Presidio','start_time': '15:00', 'end_time': '18:15','min_time': 120},
    {'person': 'Elizabeth', 'location': 'Union Square','start_time': '11:30', 'end_time': '21:00','min_time': 60},
    {'person': 'Robert', 'location': 'Financial District','start_time': '13:15', 'end_time': '15:15','min_time': 45}
]

def calculate_meeting_schedule(meetings, travel_times):
    schedule = []
    current_time = datetime.strptime('09:00', '%H:%M')
    current_location = 'The Castro'

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