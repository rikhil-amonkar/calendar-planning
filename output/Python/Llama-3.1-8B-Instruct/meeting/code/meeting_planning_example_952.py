import json
from datetime import datetime, timedelta

# Travel distances (in minutes)
travel_distances = {
    'Bayview': {
        'North Beach': 22,
        'Fisherman\'s Wharf': 25,
        'Haight-Ashbury': 19,
        'Nob Hill': 20,
        'Golden Gate Park': 22,
        'Union Square': 18,
        'Alamo Square': 16,
        'Presidio': 32,
        'Chinatown': 19,
        'Pacific Heights': 23
    },
    'North Beach': {
        'Bayview': 25,
        'Fisherman\'s Wharf': 5,
        'Haight-Ashbury': 18,
        'Nob Hill': 7,
        'Golden Gate Park': 22,
        'Union Square': 7,
        'Alamo Square': 16,
        'Presidio': 17,
        'Chinatown': 6,
        'Pacific Heights': 8
    },
    'Fisherman\'s Wharf': {
        'Bayview': 26,
        'North Beach': 6,
        'Haight-Ashbury': 22,
        'Nob Hill': 11,
        'Golden Gate Park': 25,
        'Union Square': 13,
        'Alamo Square': 21,
        'Presidio': 17,
        'Chinatown': 12,
        'Pacific Heights': 12
    },
    'Haight-Ashbury': {
        'Bayview': 18,
        'North Beach': 19,
        'Fisherman\'s Wharf': 23,
        'Nob Hill': 15,
        'Golden Gate Park': 7,
        'Union Square': 19,
        'Alamo Square': 5,
        'Presidio': 15,
        'Chinatown': 19,
        'Pacific Heights': 12
    },
    'Nob Hill': {
        'Bayview': 19,
        'North Beach': 8,
        'Fisherman\'s Wharf': 10,
        'Haight-Ashbury': 13,
        'Golden Gate Park': 17,
        'Union Square': 7,
        'Alamo Square': 11,
        'Presidio': 17,
        'Chinatown': 6,
        'Pacific Heights': 8
    },
    'Golden Gate Park': {
        'Bayview': 23,
        'North Beach': 23,
        'Fisherman\'s Wharf': 24,
        'Haight-Ashbury': 7,
        'Nob Hill': 20,
        'Union Square': 22,
        'Alamo Square': 9,
        'Presidio': 11,
        'Chinatown': 23,
        'Pacific Heights': 16
    },
    'Union Square': {
        'Bayview': 15,
        'North Beach': 10,
        'Fisherman\'s Wharf': 15,
        'Haight-Ashbury': 18,
        'Nob Hill': 9,
        'Golden Gate Park': 22,
        'Alamo Square': 15,
        'Presidio': 24,
        'Chinatown': 7,
        'Pacific Heights': 15
    },
    'Alamo Square': {
        'Bayview': 16,
        'North Beach': 15,
        'Fisherman\'s Wharf': 19,
        'Haight-Ashbury': 5,
        'Nob Hill': 11,
        'Golden Gate Park': 9,
        'Union Square': 14,
        'Presidio': 17,
        'Chinatown': 15,
        'Pacific Heights': 10
    },
    'Presidio': {
        'Bayview': 31,
        'North Beach': 18,
        'Fisherman\'s Wharf': 19,
        'Haight-Ashbury': 15,
        'Nob Hill': 18,
        'Golden Gate Park': 12,
        'Union Square': 22,
        'Alamo Square': 19,
        'Chinatown': 21,
        'Pacific Heights': 11
    },
    'Chinatown': {
        'Bayview': 20,
        'North Beach': 3,
        'Fisherman\'s Wharf': 8,
        'Haight-Ashbury': 19,
        'Nob Hill': 9,
        'Golden Gate Park': 23,
        'Union Square': 7,
        'Alamo Square': 17,
        'Presidio': 19,
        'Pacific Heights': 10
    },
    'Pacific Heights': {
        'Bayview': 22,
        'North Beach': 9,
        'Fisherman\'s Wharf': 13,
        'Haight-Ashbury': 11,
        'Nob Hill': 8,
        'Golden Gate Park': 15,
        'Union Square': 12,
        'Alamo Square': 10,
        'Presidio': 11,
        'Chinatown': 11
    }
}

# Constraints
constraints = {
    'Brian': {'start_time': datetime(2024, 7, 26, 13, 0), 'end_time': datetime(2024, 7, 26, 19, 0),'min_time': 90},
    'Richard': {'start_time': datetime(2024, 7, 26, 11, 0), 'end_time': datetime(2024, 7, 26, 12, 45),'min_time': 60},
    'Ashley': {'start_time': datetime(2024, 7, 26, 15, 0), 'end_time': datetime(2024, 7, 26, 20, 30),'min_time': 90},
    'Elizabeth': {'start_time': datetime(2024, 7, 26, 11, 45), 'end_time': datetime(2024, 7, 26, 17, 30),'min_time': 75},
    'Jessica': {'start_time': datetime(2024, 7, 26, 20, 0), 'end_time': datetime(2024, 7, 26, 21, 45),'min_time': 105},
    'Deborah': {'start_time': datetime(2024, 7, 26, 17, 30), 'end_time': datetime(2024, 7, 26, 22, 0),'min_time': 60},
    'Kimberly': {'start_time': datetime(2024, 7, 26, 17, 30), 'end_time': datetime(2024, 7, 26, 20, 15),'min_time': 45},
    'Matthew': {'start_time': datetime(2024, 7, 26, 8, 15), 'end_time': datetime(2024, 7, 26, 9, 0),'min_time': 15},
    'Kenneth': {'start_time': datetime(2024, 7, 26, 13, 45), 'end_time': datetime(2024, 7, 26, 19, 30),'min_time': 105},
    'Anthony': {'start_time': datetime(2024, 7, 26, 14, 15), 'end_time': datetime(2024, 7, 26, 16, 0),'min_time': 30}
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
            schedule.append({'action':'meet', 'location': 'Bayview', 'person': meeting_person,'start_time': current_time.strftime('%H:%M'), 'end_time': meeting_time.strftime('%H:%M')})
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

# Add travel time from Bayview to the first meeting location
schedule[0]['start_time'] = (datetime.strptime(schedule[0]['start_time'], '%H:%M') - timedelta(minutes=calculate_travel_time('Bayview', schedule[0]['location']))).strftime('%H:%M')

# Add travel time from the last meeting location to Bayview
schedule[-1]['end_time'] = (datetime.strptime(schedule[-1]['end_time'], '%H:%M') + timedelta(minutes=calculate_travel_time(schedule[-1]['location'], 'Bayview'))).strftime('%H:%M')

# Print the schedule as a JSON-formatted dictionary
print(json.dumps({'itinerary': schedule}, indent=4))