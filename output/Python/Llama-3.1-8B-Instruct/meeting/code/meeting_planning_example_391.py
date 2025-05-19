import json
from datetime import datetime, timedelta

# Travel distances (in minutes)
travel_distances = {
    'Sunset District': {
        'Alamo Square': 17,
        'Russian Hill': 24,
        'Presidio': 16,
        'Financial District': 30
    },
    'Alamo Square': {
        'Sunset District': 16,
        'Russian Hill': 13,
        'Presidio': 18,
        'Financial District': 17
    },
    'Russian Hill': {
        'Sunset District': 23,
        'Alamo Square': 15,
        'Presidio': 14,
        'Financial District': 11
    },
    'Presidio': {
        'Sunset District': 15,
        'Alamo Square': 18,
        'Russian Hill': 14,
        'Financial District': 23
    },
    'Financial District': {
        'Sunset District': 31,
        'Alamo Square': 17,
        'Russian Hill': 10,
        'Presidio': 22
    }
}

# Constraints
constraints = {
    'Kevin': {'start_time': datetime(2024, 7, 26, 8, 15), 'end_time': datetime(2024, 7, 26, 21, 30),'min_time': 75},
    'Kimberly': {'start_time': datetime(2024, 7, 26, 8, 45), 'end_time': datetime(2024, 7, 26, 12, 30),'min_time': 30},
    'Joseph': {'start_time': datetime(2024, 7, 26, 18, 30), 'end_time': datetime(2024, 7, 26, 19, 15),'min_time': 45},
    'Thomas': {'start_time': datetime(2024, 7, 26, 19, 0), 'end_time': datetime(2024, 7, 26, 21, 45),'min_time': 45}
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
            schedule.append({'action':'meet', 'location': 'Sunset District', 'person': meeting_person,'start_time': current_time.strftime('%H:%M'), 'end_time': meeting_time.strftime('%H:%M')})
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

# Add travel time from Sunset District to the first meeting location
schedule[0]['start_time'] = (datetime.strptime(schedule[0]['start_time'], '%H:%M') - timedelta(minutes=calculate_travel_time('Sunset District', schedule[0]['location']))).strftime('%H:%M')

# Add travel time from the last meeting location to Sunset District
schedule[-1]['end_time'] = (datetime.strptime(schedule[-1]['end_time'], '%H:%M') + timedelta(minutes=calculate_travel_time(schedule[-1]['location'], 'Sunset District'))).strftime('%H:%M')

# Print the schedule as a JSON-formatted dictionary
print(json.dumps({'itinerary': schedule}, indent=4))