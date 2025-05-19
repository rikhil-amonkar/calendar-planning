import json
from datetime import datetime, timedelta

# Travel distances (in minutes)
travel_distances = {
    'Union Square': {
        'The Castro': 17,
        'North Beach': 10,
        'Embarcadero': 11,
        'Alamo Square': 15,
        'Nob Hill': 9,
        'Presidio': 24,
        'Fisherman\'s Wharf': 15,
        'Mission District': 14,
        'Haight-Ashbury': 18
    },
    'The Castro': {
        'Union Square': 19,
        'North Beach': 20,
        'Embarcadero': 22,
        'Alamo Square': 8,
        'Nob Hill': 16,
        'Presidio': 20,
        'Fisherman\'s Wharf': 24,
        'Mission District': 7,
        'Haight-Ashbury': 6
    },
    'North Beach': {
        'Union Square': 7,
        'The Castro': 23,
        'Embarcadero': 6,
        'Alamo Square': 16,
        'Nob Hill': 7,
        'Presidio': 17,
        'Fisherman\'s Wharf': 5,
        'Mission District': 18,
        'Haight-Ashbury': 18
    },
    'Embarcadero': {
        'Union Square': 10,
        'The Castro': 25,
        'North Beach': 5,
        'Alamo Square': 19,
        'Nob Hill': 10,
        'Presidio': 20,
        'Fisherman\'s Wharf': 6,
        'Mission District': 20,
        'Haight-Ashbury': 21
    },
    'Alamo Square': {
        'Union Square': 14,
        'The Castro': 8,
        'North Beach': 15,
        'Embarcadero': 16,
        'Nob Hill': 11,
        'Presidio': 17,
        'Fisherman\'s Wharf': 19,
        'Mission District': 10,
        'Haight-Ashbury': 5
    },
    'Nob Hill': {
        'Union Square': 7,
        'The Castro': 17,
        'North Beach': 8,
        'Embarcadero': 9,
        'Alamo Square': 11,
        'Presidio': 17,
        'Fisherman\'s Wharf': 10,
        'Mission District': 13,
        'Haight-Ashbury': 13
    },
    'Presidio': {
        'Union Square': 22,
        'The Castro': 21,
        'North Beach': 18,
        'Embarcadero': 20,
        'Alamo Square': 19,
        'Nob Hill': 18,
        'Fisherman\'s Wharf': 19,
        'Mission District': 26,
        'Haight-Ashbury': 15
    },
    'Fisherman\'s Wharf': {
        'Union Square': 13,
        'The Castro': 27,
        'North Beach': 6,
        'Embarcadero': 8,
        'Alamo Square': 21,
        'Nob Hill': 11,
        'Presidio': 17,
        'Mission District': 22,
        'Haight-Ashbury': 22
    },
    'Mission District': {
        'Union Square': 15,
        'The Castro': 7,
        'North Beach': 17,
        'Embarcadero': 19,
        'Alamo Square': 11,
        'Nob Hill': 12,
        'Presidio': 25,
        'Fisherman\'s Wharf': 22,
        'Haight-Ashbury': 12
    },
    'Haight-Ashbury': {
        'Union Square': 19,
        'The Castro': 6,
        'North Beach': 19,
        'Embarcadero': 20,
        'Alamo Square': 5,
        'Nob Hill': 15,
        'Presidio': 15,
        'Fisherman\'s Wharf': 23,
        'Mission District': 11
    }
}

# Constraints
constraints = {
    'Melissa': {'start_time': datetime(2024, 7, 26, 20, 15), 'end_time': datetime(2024, 7, 26, 21, 15),'min_time': 30},
    'Kimberly': {'start_time': datetime(2024, 7, 26, 7, 0), 'end_time': datetime(2024, 7, 26, 10, 30),'min_time': 15},
    'Joseph': {'start_time': datetime(2024, 7, 26, 15, 30), 'end_time': datetime(2024, 7, 26, 20, 30),'min_time': 75},
    'Barbara': {'start_time': datetime(2024, 7, 26, 20, 45), 'end_time': datetime(2024, 7, 26, 21, 45),'min_time': 15},
    'Kenneth': {'start_time': datetime(2024, 7, 26, 12, 15), 'end_time': datetime(2024, 7, 26, 17, 15),'min_time': 105},
    'Joshua': {'start_time': datetime(2024, 7, 26, 16, 30), 'end_time': datetime(2024, 7, 26, 18, 15),'min_time': 105},
    'Brian': {'start_time': datetime(2024, 7, 26, 9, 30), 'end_time': datetime(2024, 7, 26, 15, 30),'min_time': 45},
    'Steven': {'start_time': datetime(2024, 7, 26, 19, 30), 'end_time': datetime(2024, 7, 26, 21, 0),'min_time': 90},
    'Betty': {'start_time': datetime(2024, 7, 26, 19, 0), 'end_time': datetime(2024, 7, 26, 20, 30),'min_time': 90}
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