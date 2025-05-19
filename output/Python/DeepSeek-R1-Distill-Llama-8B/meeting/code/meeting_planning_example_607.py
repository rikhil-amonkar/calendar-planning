# Read the input parameters and create a dictionary of travel times
travel_times = {
    'Sunset District': {
        'Russian Hill': 24,
        'The Castro': 17,
        'Richmond District': 12,
        'Marina District': 21,
        'North Beach': 29,
        'Union Square': 30,
        'Golden Gate Park': 11,
    },
    'Russian Hill': {
        'Sunset District': 23,
        'The Castro': 21,
        'Richmond District': 14,
        'Marina District': 7,
        'North Beach': 5,
        'Union Square': 11,
        'Golden Gate Park': 21,
    },
    'The Castro': {
        'Sunset District': 17,
        'Russian Hill': 18,
        'Richmond District': 16,
        'Marina District': 21,
        'North Beach': 20,
        'Union Square': 19,
        'Golden Gate Park': 11,
    },
    'Richmond District': {
        'Sunset District': 11,
        'Russian Hill': 13,
        'The Castro': 16,
        'Marina District': 9,
        'North Beach': 17,
        'Union Square': 21,
        'Golden Gate Park': 9,
    },
    'Marina District': {
        'Sunset District': 19,
        'Russian Hill': 8,
        'The Castro': 22,
        'Richmond District': 11,
        'North Beach': 11,
        'Union Square': 16,
        'Golden Gate Park': 18,
    },
    'North Beach': {
        'Sunset District': 27,
        'Russian Hill': 4,
        'The Castro': 22,
        'Richmond District': 18,
        'Marina District': 11,
        'Union Square': 7,
        'Golden Gate Park': 22,
    },
    'Union Square': {
        'Sunset District': 26,
        'Russian Hill': 13,
        'The Castro': 19,
        'Richmond District': 20,
        'Marina District': 18,
        'North Beach': 10,
        'Golden Gate Park': 22,
    },
    'Golden Gate Park': {
        'Sunset District': 10,
        'Russian Hill': 19,
        'The Castro': 13,
        'Richmond District': 7,
        'Marina District': 16,
        'North Beach': 24,
        'Union Square': 22,
    }
}

# Define the current location and time
current_location = 'Sunset District'
current_time = '9:00'

itinerary = []

# List of people with their constraints
people = [
    {'name': 'Karen', 'location': 'Russian Hill', 'start': '20:45', 'end': '21:45', 'duration': 60},
    {'name': 'Jessica', 'location': 'The Castro', 'start': '14:45', 'end': '19:30', 'duration': 60},
    {'name': 'Matthew', 'location': 'Richmond District', 'start': '7:30', 'end': '13:15', 'duration': 15},
    {'name': 'Michelle', 'location': 'Marina District', 'start': '10:30', 'end': '17:45', 'duration': 75},
    {'name': 'Carol', 'location': 'North Beach', 'start': '12:00', 'end': '17:00', 'duration': 90},
    {'name': 'Stephanie', 'location': 'Union Square', 'start': '10:45', 'end': '13:15', 'duration': 30},
    {'name': 'Linda', 'location': 'Golden Gate Park', 'start': '10:45', 'end': '22:00', 'duration': 90},
]

# Sort people by duration in descending order
people_sorted = sorted(people, key=lambda x: -x['duration'])

import datetime

for person in people_sorted:
    # Calculate the latest possible start time considering current location and travel time
    location = person['location']
    if current_location not in travel_times:
        continue  # Skip if current location is not in the travel times
    if location not in travel_times[current_location]:
        continue  # Skip if location is not reachable from current location
    travel_time = travel_times[current_location][location]
    
    # Convert current_time to datetime object
    current_dt = datetime.datetime.strptime(current_time, "%H:%M")
    
    # Calculate earliest possible start time
    earliest_possible_start = current_dt + datetime.timedelta(minutes=travel_time)
    earliest_possible_start = earliest_possible_start.replace(second=0, microsecond=0)
    
    # Check if earliest possible start is within the person's availability
    start_dt = datetime.datetime.strptime(person['start'], "%H:%M")
    end_dt = datetime.datetime.strptime(person['end'], "%H:%M")
    
    if earliest_possible_start > end_dt:
        continue  # Not possible to meet this person
    
    # Ensure that the meeting duration fits within the person's availability
    if (end_dt - earliest_possible_start).total_seconds() < (person['duration'] * 60):
        continue  # Not enough time to meet
    
    # Calculate the latest possible start time to maximize remaining time
    latest_possible_start = end_dt - datetime.timedelta(minutes=person['duration'])
    if latest_possible_start < current_dt:
        latest_possible_start = current_dt
    
    # Choose the latest possible start time
    start_dt = latest_possible_start
    
    # Check if the calculated start time is valid
    if start_dt < current_dt:
        continue  # Not possible to meet this person
    
    # Create the meeting entry
    meeting = {
        'action': 'meet',
        'location': location,
        'person': person['name'],
        'start_time': start_dt.strftime("%H:%M"),
        'end_time': (start_dt + datetime.timedelta(minutes=person['duration'])).strftime("%H:%MM")
    }
    itinerary.append(meeting)
    
    # Update current location and time
    current_location = location
    current_time = meeting['end_time']

# Convert the itinerary to JSON format
import json
print(json.dumps(itinerary))