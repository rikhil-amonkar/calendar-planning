import json
from datetime import datetime, timedelta

# Travel distances (in minutes)
travel_distances = {
    'The Castro': {
        'Bayview': 19,
        'Pacific Heights': 16,
        'Alamo Square': 8,
        'Fisherman\'s Wharf': 24,
        'Golden Gate Park': 11
    },
    'Bayview': {
        'The Castro': 20,
        'Pacific Heights': 23,
        'Alamo Square': 16,
        'Fisherman\'s Wharf': 25,
        'Golden Gate Park': 22
    },
    'Pacific Heights': {
        'The Castro': 16,
        'Bayview': 22,
        'Alamo Square': 10,
        'Fisherman\'s Wharf': 13,
        'Golden Gate Park': 15
    },
    'Alamo Square': {
        'The Castro': 8,
        'Bayview': 16,
        'Pacific Heights': 10,
        'Fisherman\'s Wharf': 19,
        'Golden Gate Park': 9
    },
    'Fisherman\'s Wharf': {
        'The Castro': 26,
        'Bayview': 26,
        'Pacific Heights': 12,
        'Alamo Square': 20,
        'Golden Gate Park': 25
    },
    'Golden Gate Park': {
        'The Castro': 13,
        'Bayview': 23,
        'Pacific Heights': 16,
        'Alamo Square': 10,
        'Fisherman\'s Wharf': 24
    }
}

# Constraints
constraints = {
    'Rebecca': {'start_time': datetime(2024, 7, 26, 9, 0), 'end_time': datetime(2024, 7, 26, 12, 45),'min_time': 90},
    'Amanda': {'start_time': datetime(2024, 7, 26, 18, 30), 'end_time': datetime(2024, 7, 26, 21, 45),'min_time': 90},
    'James': {'start_time': datetime(2024, 7, 26, 9, 45), 'end_time': datetime(2024, 7, 26, 21, 15),'min_time': 90},
    'Sarah': {'start_time': datetime(2024, 7, 26, 8, 0), 'end_time': datetime(2024, 7, 26, 21, 30),'min_time': 90},
    'Melissa': {'start_time': datetime(2024, 7, 26, 9, 0), 'end_time': datetime(2024, 7, 26, 18, 45),'min_time': 90}
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
            schedule.append({'action':'meet', 'location': 'The Castro', 'person': meeting_person,'start_time': current_time.strftime('%H:%M'), 'end_time': meeting_time.strftime('%H:%M')})
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

# Add travel time from The Castro to the first meeting location
schedule[0]['start_time'] = (datetime.strptime(schedule[0]['start_time'], '%H:%M') - timedelta(minutes=calculate_travel_time('The Castro', schedule[0]['location']))).strftime('%H:%M')

# Add travel time from the last meeting location to The Castro
schedule[-1]['end_time'] = (datetime.strptime(schedule[-1]['end_time'], '%H:%M') + timedelta(minutes=calculate_travel_time(schedule[-1]['location'], 'The Castro'))).strftime('%H:%M')

# Print the schedule as a JSON-formatted dictionary
print(json.dumps({'itinerary': schedule}, indent=4))