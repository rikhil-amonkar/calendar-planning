import json
from datetime import datetime, timedelta

# Travel distances (in minutes)
travel_distances = {
    'Pacific Heights': {
        'Marina District': 6,
        'The Castro': 16,
        'Richmond District': 12,
        'Alamo Square': 10,
        'Financial District': 13,
        'Presidio': 11,
        'Mission District': 15,
        'Nob Hill': 8,
        'Russian Hill': 7
    },
    'Marina District': {
        'Pacific Heights': 7,
        'The Castro': 22,
        'Richmond District': 11,
        'Alamo Square': 15,
        'Financial District': 17,
        'Presidio': 10,
        'Mission District': 20,
        'Nob Hill': 12,
        'Russian Hill': 8
    },
    'The Castro': {
        'Pacific Heights': 16,
        'Marina District': 21,
        'Richmond District': 16,
        'Alamo Square': 8,
        'Financial District': 21,
        'Presidio': 20,
        'Mission District': 7,
        'Nob Hill': 16,
        'Russian Hill': 18
    },
    'Richmond District': {
        'Pacific Heights': 10,
        'Marina District': 9,
        'The Castro': 16,
        'Alamo Square': 13,
        'Financial District': 22,
        'Presidio': 7,
        'Mission District': 20,
        'Nob Hill': 17,
        'Russian Hill': 13
    },
    'Alamo Square': {
        'Pacific Heights': 10,
        'Marina District': 15,
        'The Castro': 8,
        'Richmond District': 11,
        'Financial District': 17,
        'Presidio': 17,
        'Mission District': 10,
        'Nob Hill': 11,
        'Russian Hill': 13
    },
    'Financial District': {
        'Pacific Heights': 13,
        'Marina District': 15,
        'The Castro': 20,
        'Richmond District': 21,
        'Alamo Square': 17,
        'Presidio': 22,
        'Mission District': 17,
        'Nob Hill': 8,
        'Russian Hill': 11
    },
    'Presidio': {
        'Pacific Heights': 11,
        'Marina District': 11,
        'The Castro': 21,
        'Richmond District': 7,
        'Alamo Square': 19,
        'Financial District': 23,
        'Mission District': 26,
        'Nob Hill': 18,
        'Russian Hill': 14
    },
    'Mission District': {
        'Pacific Heights': 16,
        'Marina District': 19,
        'The Castro': 7,
        'Richmond District': 20,
        'Alamo Square': 11,
        'Financial District': 15,
        'Presidio': 25,
        'Nob Hill': 12,
        'Russian Hill': 15
    },
    'Nob Hill': {
        'Pacific Heights': 8,
        'Marina District': 11,
        'The Castro': 17,
        'Richmond District': 14,
        'Alamo Square': 11,
        'Financial District': 9,
        'Presidio': 17,
        'Mission District': 13,
        'Russian Hill': 5
    },
    'Russian Hill': {
        'Pacific Heights': 7,
        'Marina District': 7,
        'The Castro': 21,
        'Richmond District': 14,
        'Alamo Square': 15,
        'Financial District': 11,
        'Presidio': 14,
        'Mission District': 16,
        'Nob Hill': 5
    }
}

# Constraints
constraints = {
    'Linda': {'start_time': datetime(2024, 7, 26, 18, 0), 'end_time': datetime(2024, 7, 26, 20, 0),'min_time': 30},
    'Kenneth': {'start_time': datetime(2024, 7, 26, 14, 45), 'end_time': datetime(2024, 7, 26, 16, 15),'min_time': 30},
    'Kimberly': {'start_time': datetime(2024, 7, 26, 14, 15), 'end_time': datetime(2024, 7, 26, 20, 0),'min_time': 30},
    'Paul': {'start_time': datetime(2024, 7, 26, 21, 0), 'end_time': datetime(2024, 7, 26, 21, 45),'min_time': 15},
    'Carol': {'start_time': datetime(2024, 7, 26, 10, 15), 'end_time': datetime(2024, 7, 26, 12, 0),'min_time': 60},
    'Brian': {'start_time': datetime(2024, 7, 26, 10, 0), 'end_time': datetime(2024, 7, 26, 21, 30),'min_time': 75},
    'Laura': {'start_time': datetime(2024, 7, 26, 16, 15), 'end_time': datetime(2024, 7, 26, 20, 30),'min_time': 30},
    'Sandra': {'start_time': datetime(2024, 7, 26, 9, 15), 'end_time': datetime(2024, 7, 26, 18, 30),'min_time': 60},
    'Karen': {'start_time': datetime(2024, 7, 26, 18, 30), 'end_time': datetime(2024, 7, 26, 20, 30),'min_time': 75}
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
            schedule.append({'action':'meet', 'location': 'Pacific Heights', 'person': meeting_person,'start_time': current_time.strftime('%H:%M'), 'end_time': meeting_time.strftime('%H:%M')})
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

# Add travel time from Pacific Heights to the first meeting location
schedule[0]['start_time'] = (datetime.strptime(schedule[0]['start_time'], '%H:%M') - timedelta(minutes=calculate_travel_time('Pacific Heights', schedule[0]['location']))).strftime('%H:%M')

# Add travel time from the last meeting location to Pacific Heights
schedule[-1]['end_time'] = (datetime.strptime(schedule[-1]['end_time'], '%H:%M') + timedelta(minutes=calculate_travel_time(schedule[-1]['location'], 'Pacific Heights'))).strftime('%H:%M')

# Print the schedule as a JSON-formatted dictionary
print(json.dumps({'itinerary': schedule}, indent=4))