import json
from datetime import datetime, timedelta

# Travel distances (in minutes)
travel_distances = {
    'Union Square': {
        'Mission District': 14,
        'Fisherman\'s Wharf': 15,
        'Russian Hill': 13,
        'Marina District': 18,
        'North Beach': 10,
        'Chinatown': 7,
        'Pacific Heights': 15,
        'The Castro': 17,
        'Nob Hill': 9,
        'Sunset District': 27
    },
    'Mission District': {
        'Union Square': 15,
        'Fisherman\'s Wharf': 22,
        'Russian Hill': 15,
        'Marina District': 19,
        'North Beach': 17,
        'Chinatown': 16,
        'Pacific Heights': 16,
        'The Castro': 7,
        'Nob Hill': 12,
        'Sunset District': 24
    },
    'Fisherman\'s Wharf': {
        'Union Square': 13,
        'Mission District': 22,
        'Russian Hill': 7,
        'Marina District': 9,
        'North Beach': 6,
        'Chinatown': 12,
        'Pacific Heights': 12,
        'The Castro': 27,
        'Nob Hill': 11,
        'Sunset District': 27
    },
    'Russian Hill': {
        'Union Square': 10,
        'Mission District': 16,
        'Fisherman\'s Wharf': 7,
        'Marina District': 7,
        'North Beach': 5,
        'Chinatown': 9,
        'Pacific Heights': 7,
        'The Castro': 21,
        'Nob Hill': 5,
        'Sunset District': 23
    },
    'Marina District': {
        'Union Square': 16,
        'Mission District': 20,
        'Fisherman\'s Wharf': 10,
        'Russian Hill': 8,
        'North Beach': 11,
        'Chinatown': 15,
        'Pacific Heights': 7,
        'The Castro': 22,
        'Nob Hill': 12,
        'Sunset District': 19
    },
    'North Beach': {
        'Union Square': 7,
        'Mission District': 18,
        'Fisherman\'s Wharf': 5,
        'Russian Hill': 4,
        'Marina District': 9,
        'Chinatown': 6,
        'Pacific Heights': 8,
        'The Castro': 23,
        'Nob Hill': 7,
        'Sunset District': 27
    },
    'Chinatown': {
        'Union Square': 7,
        'Mission District': 17,
        'Fisherman\'s Wharf': 8,
        'Russian Hill': 7,
        'Marina District': 12,
        'North Beach': 3,
        'Pacific Heights': 10,
        'The Castro': 22,
        'Nob Hill': 9,
        'Sunset District': 29
    },
    'Pacific Heights': {
        'Union Square': 12,
        'Mission District': 15,
        'Fisherman\'s Wharf': 13,
        'Russian Hill': 7,
        'Marina District': 6,
        'North Beach': 9,
        'Chinatown': 11,
        'The Castro': 16,
        'Nob Hill': 8,
        'Sunset District': 21
    },
    'The Castro': {
        'Union Square': 19,
        'Mission District': 7,
        'Fisherman\'s Wharf': 24,
        'Russian Hill': 18,
        'Marina District': 21,
        'North Beach': 20,
        'Chinatown': 22,
        'Pacific Heights': 16,
        'Nob Hill': 16,
        'Sunset District': 17
    },
    'Nob Hill': {
        'Union Square': 7,
        'Mission District': 13,
        'Fisherman\'s Wharf': 10,
        'Russian Hill': 5,
        'Marina District': 11,
        'North Beach': 8,
        'Chinatown': 6,
        'Pacific Heights': 8,
        'The Castro': 17,
        'Sunset District': 27
    },
    'Sunset District': {
        'Union Square': 30,
        'Mission District': 25,
        'Fisherman\'s Wharf': 29,
        'Russian Hill': 24,
        'Marina District': 21,
        'North Beach': 28,
        'Chinatown': 30,
        'Pacific Heights': 21,
        'The Castro': 17,
        'Nob Hill': 27
    }
}

# Constraints
constraints = {
    'Kevin': {'start_time': datetime(2024, 7, 26, 20, 45), 'end_time': datetime(2024, 7, 26, 21, 45),'min_time': 60},
    'Mark': {'start_time': datetime(2024, 7, 26, 17, 15), 'end_time': datetime(2024, 7, 26, 20, 0),'min_time': 90},
    'Jessica': {'start_time': datetime(2024, 7, 26, 9, 0), 'end_time': datetime(2024, 7, 26, 15, 0),'min_time': 120},
    'Jason': {'start_time': datetime(2024, 7, 26, 15, 15), 'end_time': datetime(2024, 7, 26, 21, 45),'min_time': 120},
    'John': {'start_time': datetime(2024, 7, 26, 9, 45), 'end_time': datetime(2024, 7, 26, 12, 0),'min_time': 15},
    'Karen': {'start_time': datetime(2024, 7, 26, 16, 45), 'end_time': datetime(2024, 7, 26, 19, 0),'min_time': 75},
    'Sarah': {'start_time': datetime(2024, 7, 26, 17, 30), 'end_time': datetime(2024, 7, 26, 18, 15),'min_time': 45},
    'Amanda': {'start_time': datetime(2024, 7, 26, 20, 0), 'end_time': datetime(2024, 7, 26, 21, 15),'min_time': 60},
    'Nancy': {'start_time': datetime(2024, 7, 26, 9, 45), 'end_time': datetime(2024, 7, 26, 13, 0),'min_time': 45},
    'Rebecca': {'start_time': datetime(2024, 7, 26, 8, 45), 'end_time': datetime(2024, 7, 26, 13, 0),'min_time': 75}
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
            schedule.append({'action':'meet', 'location': 'Union Square', 'person': meeting_person,'start_time': current_time.strftime('%H:%M'), 'end_time': meeting_time.strftime('%H:%M')})
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

# Add travel time from Union Square to the first meeting location
schedule[0]['start_time'] = (datetime.strptime(schedule[0]['start_time'], '%H:%M') - timedelta(minutes=calculate_travel_time('Union Square', schedule[0]['location']))).strftime('%H:%M')

# Add travel time from the last meeting location to Union Square
schedule[-1]['end_time'] = (datetime.strptime(schedule[-1]['end_time'], '%H:%M') + timedelta(minutes=calculate_travel_time(schedule[-1]['location'], 'Union Square'))).strftime('%H:%M')

# Print the schedule as a JSON-formatted dictionary
print(json.dumps({'itinerary': schedule}, indent=4))