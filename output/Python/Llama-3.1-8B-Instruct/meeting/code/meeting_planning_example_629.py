import json
from datetime import datetime, timedelta

# Travel distances (in minutes)
travel_distances = {
    'Russian Hill': {
        'Presidio': 14,
        'Chinatown': 9,
        'Pacific Heights': 7,
        'Richmond District': 14,
        'Fisherman\'s Wharf': 7,
        'Golden Gate Park': 21,
        'Bayview': 23
    },
    'Presidio': {
        'Russian Hill': 14,
        'Chinatown': 21,
        'Pacific Heights': 11,
        'Richmond District': 7,
        'Fisherman\'s Wharf': 19,
        'Golden Gate Park': 12,
        'Bayview': 31
    },
    'Chinatown': {
        'Russian Hill': 7,
        'Presidio': 19,
        'Pacific Heights': 10,
        'Richmond District': 20,
        'Fisherman\'s Wharf': 8,
        'Golden Gate Park': 23,
        'Bayview': 22
    },
    'Pacific Heights': {
        'Russian Hill': 7,
        'Presidio': 11,
        'Chinatown': 11,
        'Richmond District': 12,
        'Fisherman\'s Wharf': 13,
        'Golden Gate Park': 15,
        'Bayview': 22
    },
    'Richmond District': {
        'Russian Hill': 13,
        'Presidio': 7,
        'Chinatown': 20,
        'Pacific Heights': 10,
        'Fisherman\'s Wharf': 18,
        'Golden Gate Park': 9,
        'Bayview': 26
    },
    'Fisherman\'s Wharf': {
        'Russian Hill': 7,
        'Presidio': 17,
        'Chinatown': 12,
        'Pacific Heights': 12,
        'Richmond District': 18,
        'Golden Gate Park': 25,
        'Bayview': 26
    },
    'Golden Gate Park': {
        'Russian Hill': 19,
        'Presidio': 11,
        'Chinatown': 23,
        'Pacific Heights': 16,
        'Richmond District': 7,
        'Fisherman\'s Wharf': 24,
        'Bayview': 23
    },
    'Bayview': {
        'Russian Hill': 23,
        'Presidio': 31,
        'Chinatown': 18,
        'Pacific Heights': 23,
        'Richmond District': 25,
        'Fisherman\'s Wharf': 25,
        'Golden Gate Park': 22
    }
}

# Constraints
constraints = {
    'Matthew': {'start_time': datetime(2024, 7, 26, 11, 0), 'end_time': datetime(2024, 7, 26, 21, 0),'min_time': 90},
    'Margaret': {'start_time': datetime(2024, 7, 26, 9, 15), 'end_time': datetime(2024, 7, 26, 18, 45),'min_time': 90},
    'Nancy': {'start_time': datetime(2024, 7, 26, 14, 15), 'end_time': datetime(2024, 7, 26, 17, 0),'min_time': 15},
    'Helen': {'start_time': datetime(2024, 7, 26, 19, 45), 'end_time': datetime(2024, 7, 26, 22, 0),'min_time': 60},
    'Rebecca': {'start_time': datetime(2024, 7, 26, 21, 15), 'end_time': datetime(2024, 7, 26, 22, 15),'min_time': 60},
    'Kimberly': {'start_time': datetime(2024, 7, 26, 13, 0), 'end_time': datetime(2024, 7, 26, 16, 30),'min_time': 120},
    'Kenneth': {'start_time': datetime(2024, 7, 26, 14, 30), 'end_time': datetime(2024, 7, 26, 18, 0),'min_time': 60}
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
            schedule.append({'action':'meet', 'location': 'Russian Hill', 'person': meeting_person,'start_time': current_time.strftime('%H:%M'), 'end_time': meeting_time.strftime('%H:%M')})
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

# Add travel time from Russian Hill to the first meeting location
schedule[0]['start_time'] = (datetime.strptime(schedule[0]['start_time'], '%H:%M') - timedelta(minutes=calculate_travel_time('Russian Hill', schedule[0]['location']))).strftime('%H:%M')

# Add travel time from the last meeting location to Russian Hill
schedule[-1]['end_time'] = (datetime.strptime(schedule[-1]['end_time'], '%H:%M') + timedelta(minutes=calculate_travel_time(schedule[-1]['location'], 'Russian Hill'))).strftime('%H:%M')

# Print the schedule as a JSON-formatted dictionary
print(json.dumps({'itinerary': schedule}, indent=4))