import json
from datetime import datetime, timedelta

# Travel distances (in minutes)
travel_distances = {
    'Embarcadero': {
        'Golden Gate Park': 25,
        'Haight-Ashbury': 21,
        'Bayview': 21,
        'Presidio': 20,
        'Financial District': 5
    },
    'Golden Gate Park': {
        'Embarcadero': 25,
        'Haight-Ashbury': 7,
        'Bayview': 23,
        'Presidio': 11,
        'Financial District': 26
    },
    'Haight-Ashbury': {
        'Embarcadero': 20,
        'Golden Gate Park': 7,
        'Bayview': 19,
        'Presidio': 15,
        'Financial District': 21
    },
    'Bayview': {
        'Embarcadero': 19,
        'Golden Gate Park': 22,
        'Haight-Ashbury': 19,
        'Presidio': 31,
        'Financial District': 19
    },
    'Presidio': {
        'Embarcadero': 20,
        'Golden Gate Park': 12,
        'Haight-Ashbury': 15,
        'Bayview': 31,
        'Financial District': 23
    },
    'Financial District': {
        'Embarcadero': 4,
        'Golden Gate Park': 23,
        'Haight-Ashbury': 19,
        'Bayview': 19,
        'Presidio': 22
    }
}

# Constraints
constraints = {
    'Mary': {'start_time': datetime(2024, 7, 26, 8, 45), 'end_time': datetime(2024, 7, 26, 11, 45),'min_time': 45},
    'Kevin': {'start_time': datetime(2024, 7, 26, 10, 15), 'end_time': datetime(2024, 7, 26, 16, 15),'min_time': 90},
    'Deborah': {'start_time': datetime(2024, 7, 26, 15, 0), 'end_time': datetime(2024, 7, 26, 19, 15),'min_time': 120},
    'Stephanie': {'start_time': datetime(2024, 7, 26, 10, 0), 'end_time': datetime(2024, 7, 26, 17, 15),'min_time': 120},
    'Emily': {'start_time': datetime(2024, 7, 26, 11, 30), 'end_time': datetime(2024, 7, 26, 21, 45),'min_time': 105}
}

# Start time
start_time = datetime(2024, 7, 26, 9, 0)

# Function to calculate travel time
def calculate_travel_time(start_location, end_location):
    return travel_distances[start_location][end_location]

# Function to check if a meeting is possible
def is_meeting_possible(meeting_start_time, meeting_end_time, person):
    person_start_time = constraints[person]['start_time']
    person_end_time = constraints[person]['end_time']
    min_time = constraints[person]['min_time']
    return (meeting_start_time >= person_start_time and meeting_start_time <= person_end_time) or \
           (meeting_end_time >= person_start_time and meeting_end_time <= person_end_time) or \
           (person_start_time <= meeting_start_time and person_end_time >= meeting_end_time and meeting_end_time - meeting_start_time >= timedelta(minutes=min_time))

# Function to find the optimal meeting schedule
def find_optimal_schedule():
    schedule = []
    current_time = start_time
    while current_time < datetime(2024, 7, 26, 23, 59):
        possible_meetings = []
        for person in constraints:
            if is_meeting_possible(current_time, current_time + timedelta(minutes=60), person):
                possible_meetings.append(person)
        if possible_meetings:
            meeting_person = max(possible_meetings, key=lambda person: constraints[person]['min_time'])
            meeting_time = current_time + timedelta(minutes=constraints[meeting_person]['min_time'])
            schedule.append({'action':'meet', 'location': 'Embarcadero', 'person': meeting_person,'start_time': current_time.strftime('%H:%M'), 'end_time': meeting_time.strftime('%H:%M')})
            current_time = meeting_time
        else:
            current_time += timedelta(minutes=1)
    return schedule

# Find the optimal meeting schedule
schedule = find_optimal_schedule()

# Add travel times to the schedule
for i in range(len(schedule) - 1):
    start_location = schedule[i]['location']
    end_location = schedule[i+1]['location']
    travel_time = calculate_travel_time(start_location, end_location)
    schedule[i]['end_time'] = (datetime.strptime(schedule[i]['end_time'], '%H:%M') + timedelta(minutes=travel_time)).strftime('%H:%M')
    schedule[i+1]['start_time'] = (datetime.strptime(schedule[i+1]['start_time'], '%H:%M') - timedelta(minutes=travel_time)).strftime('%H:%M')

# Add travel time from Embarcadero to the first meeting location
schedule[0]['start_time'] = (datetime.strptime(schedule[0]['start_time'], '%H:%M') - timedelta(minutes=calculate_travel_time('Embarcadero', schedule[0]['location']))).strftime('%H:%M')

# Add travel time from the last meeting location to Embarcadero
schedule[-1]['end_time'] = (datetime.strptime(schedule[-1]['end_time'], '%H:%M') + timedelta(minutes=calculate_travel_time(schedule[-1]['location'], 'Embarcadero'))).strftime('%H:%M')

# Print the schedule as a JSON-formatted dictionary
print(json.dumps({'itinerary': schedule}, indent=4))