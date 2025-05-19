# Read the input parameters and create a dictionary of travel times
travel_times = {
    'Financial District': {
        'Fisherman\'s Wharf': 10,
        'Presidio': 22,
        'Bayview': 19,
        'Haight-Ashbury': 19,
        'Russian Hill': 11,
        'The Castro': 20,
        'Marina District': 15,
        'Richmond District': 21,
        'Union Square': 9,
        'Sunset District': 30,
    },
    'Fisherman\'s Wharf': {
        'Financial District': 11,
        'Presidio': 17,
        'Bayview': 26,
        'Haight-Ashbury': 22,
        'Russian Hill': 7,
        'The Castro': 27,
        'Marina District': 9,
        'Richmond District': 18,
        'Union Square': 13,
        'Sunset District': 27,
    },
    'Presidio': {
        'Financial District': 23,
        'Fisherman\'s Wharf': 19,
        'Bayview': 32,
        'Haight-Ashbury': 15,
        'Russian Hill': 14,
        'The Castro': 21,
        'Marina District': 11,
        'Richmond District': 7,
        'Union Square': 22,
        'Sunset District': 15,
    },
    'Bayview': {
        'Financial District': 19,
        'Fisherman\'s Wharf': 25,
        'Presidio': 32,
        'Haight-Ashbury': 19,
        'Russian Hill': 23,
        'The Castro': 19,
        'Marina District': 27,
        'Richmond District': 25,
        'Union Square': 18,
        'Sunset District': 23,
    },
    'Haight-Ashbury': {
        'Financial District': 21,
        'Fisherman\'s Wharf': 23,
        'Presidio': 15,
        'Bayview': 18,
        'Russian Hill': 17,
        'The Castro': 6,
        'Marina District': 17,
        'Richmond District': 10,
        'Union Square': 19,
        'Sunset District': 15,
    },
    'Russian Hill': {
        'Financial District': 11,
        'Fisherman\'s Wharf': 7,
        'Presidio': 14,
        'Bayview': 23,
        'Haight-Ashbury': 17,
        'The Castro': 21,
        'Marina District': 7,
        'Richmond District': 14,
        'Union Square': 10,
        'Sunset District': 23,
    },
    'The Castro': {
        'Financial District': 21,
        'Fisherman\'s Wharf': 24,
        'Presidio': 20,
        'Bayview': 19,
        'Haight-Ashbury': 6,
        'Marina District': 21,
        'Richmond District': 16,
        'Union Square': 19,
        'Sunset District': 17,
    },
    'Marina District': {
        'Financial District': 17,
        'Fisherman\'s Wharf': 10,
        'Presidio': 10,
        'Bayview': 27,
        'Haight-Ashbury': 16,
        'Russian Hill': 8,
        'The Castro': 22,
        'Richmond District': 11,
        'Union Square': 16,
        'Sunset District': 19,
    },
    'Richmond District': {
        'Financial District': 22,
        'Fisherman\'s Wharf': 18,
        'Presidio': 7,
        'Bayview': 27,
        'Haight-Ashbury': 10,
        'Russian Hill': 13,
        'The Castro': 16,
        'Union Square': 21,
        'Sunset District': 11,
    },
    'Union Square': {
        'Financial District': 9,
        'Fisherman\'s Wharf': 15,
        'Presidio': 24,
        'Bayview': 15,
        'Haight-Ashbury': 18,
        'Russian Hill': 13,
        'The Castro': 17,
        'Marina District': 18,
        'Richmond District': 20,
        'Sunset District': 27,
    },
    'Sunset District': {
        'Financial District': 30,
        'Fisherman\'s Wharf': 29,
        'Presidio': 16,
        'Bayview': 22,
        'Haight-Ashbury': 15,
        'Russian Hill': 24,
        'The Castro': 17,
        'Marina District': 21,
        'Richmond District': 12,
        'Union Square': 30,
    }
}

# Define the current location and time
current_location = 'Financial District'
current_time = '9:00'

itinerary = []

# List of people with their constraints
people = [
    {'name': 'Mark', 'location': 'Fisherman\'s Wharf', 'start': '8:15', 'end': '10:00', 'duration': 30},
    {'name': 'Stephanie', 'location': 'Presidio', 'start': '12:15', 'end': '15:00', 'duration': 75},
    {'name': 'Betty', 'location': 'Bayview', 'start': '7:15', 'end': '20:30', 'duration': 15},
    {'name': 'Lisa', 'location': 'Haight-Ashbury', 'start': '14:30', 'end': '19:30', 'duration': 45},
    {'name': 'William', 'location': 'Russian Hill', 'start': '18:45', 'end': '20:00', 'duration': 60},
    {'name': 'Brian', 'location': 'The Castro', 'start': '9:15', 'end': '10:15', 'duration': 30},
    {'name': 'Joseph', 'location': 'Marina District', 'start': '10:45', 'end': '15:00', 'duration': 90},
    {'name': 'Ashley', 'location': 'Richmond District', 'start': '9:45', 'end': '11:15', 'duration': 45},
    {'name': 'Patricia', 'location': 'Union Square', 'start': '16:30', 'end': '20:00', 'duration': 120},
    {'name': 'Karen', 'location': 'Sunset District', 'start': '16:30', 'end': '22:00', 'duration': 105},
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
        'end_time': (start_dt + datetime.timedelta(minutes=person['duration'])).strftime("%H:%M")
    }
    itinerary.append(meeting)
    
    # Update current location and time
    current_location = location
    current_time = meeting['end_time']

# Convert the itinerary to JSON format
import json
print(json.dumps(itinerary))