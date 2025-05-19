# Read the input parameters and create a dictionary of travel times
travel_times = {
    'Bayview': {
        'Nob Hill': 20,
        'Union Square': 17,
        'Chinatown': 18,
        'The Castro': 20,
        'Presidio': 31,
        'Pacific Heights': 23,
        'Russian Hill': 23,
    },
    'Nob Hill': {
        'Bayview': 19,
        'Union Square': 7,
        'Chinatown': 6,
        'The Castro': 17,
        'Presidio': 17,
        'Pacific Heights': 8,
        'Russian Hill': 5,
    },
    'Union Square': {
        'Bayview': 15,
        'Nob Hill': 9,
        'Chinatown': 7,
        'The Castro': 19,
        'Presidio': 24,
        'Pacific Heights': 15,
        'Russian Hill': 13,
    },
    'Chinatown': {
        'Bayview': 22,
        'Nob Hill': 8,
        'Union Square': 7,
        'The Castro': 22,
        'Presidio': 19,
        'Pacific Heights': 10,
        'Russian Hill': 7,
    },
    'The Castro': {
        'Bayview': 19,
        'Nob Hill': 16,
        'Union Square': 19,
        'Chinatown': 20,
        'Presidio': 20,
        'Pacific Heights': 16,
        'Russian Hill': 18,
    },
    'Presidio': {
        'Bayview': 31,
        'Nob Hill': 18,
        'Union Square': 22,
        'Chinatown': 21,
        'The Castro': 21,
        'Pacific Heights': 11,
        'Russian Hill': 14,
    },
    'Pacific Heights': {
        'Bayview': 22,
        'Nob Hill': 8,
        'Union Square': 12,
        'Chinatown': 11,
        'The Castro': 16,
        'Presidio': 11,
        'Russian Hill': 7,
    },
    'Russian Hill': {
        'Bayview': 23,
        'Nob Hill': 5,
        'Union Square': 11,
        'Chinatown': 9,
        'The Castro': 21,
        'Presidio': 14,
        'Pacific Heights': 7,
    }
}

# Define the current location and time
current_location = 'Bayview'
current_time = '9:00'

itinerary = []

# List of people with their constraints
people = [
    {'name': 'Paul', 'location': 'Nob Hill', 'start': '16:15', 'end': '21:15', 'duration': 60},
    {'name': 'Carol', 'location': 'Union Square', 'start': '18:00', 'end': '20:15', 'duration': 120},
    {'name': 'Patricia', 'location': 'Chinatown', 'start': '20:00', 'end': '21:30', 'duration': 75},
    {'name': 'Karen', 'location': 'The Castro', 'start': '17:00', 'end': '19:00', 'duration': 45},
    {'name': 'Nancy', 'location': 'Presidio', 'start': '11:45', 'end': '22:00', 'duration': 30},
    {'name': 'Jeffrey', 'location': 'Pacific Heights', 'start': '20:00', 'end': '20:45', 'duration': 45},
    {'name': 'Matthew', 'location': 'Russian Hill', 'start': '15:45', 'end': '21:45', 'duration': 75},
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