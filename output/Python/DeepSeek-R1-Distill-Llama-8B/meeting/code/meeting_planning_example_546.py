# Read the input parameters and create a dictionary of travel times
travel_times = {
    'Embarcadero': {
        'Richmond District': 21,
        'Union Square': 10,
        'Financial District': 5,
        'Pacific Heights': 11,
        'Nob Hill': 10,
        'Bayview': 21,
    },
    'Richmond District': {
        'Embarcadero': 19,
        'Union Square': 21,
        'Financial District': 22,
        'Pacific Heights': 10,
        'Nob Hill': 17,
        'Bayview': 26,
    },
    'Union Square': {
        'Embarcadero': 11,
        'Richmond District': 20,
        'Financial District': 9,
        'Pacific Heights': 15,
        'Nob Hill': 9,
        'Bayview': 15,
    },
    'Financial District': {
        'Embarcadero': 4,
        'Richmond District': 21,
        'Union Square': 9,
        'Pacific Heights': 13,
        'Nob Hill': 8,
        'Bayview': 19,
    },
    'Pacific Heights': {
        'Embarcadero': 10,
        'Richmond District': 12,
        'Union Square': 12,
        'Financial District': 13,
        'Nob Hill': 8,
        'Bayview': 22,
    },
    'Nob Hill': {
        'Embarcadero': 9,
        'Richmond District': 14,
        'Union Square': 7,
        'Financial District': 9,
        'Pacific Heights': 8,
        'Bayview': 19,
    },
    'Bayview': {
        'Embarcadero': 19,
        'Richmond District': 25,
        'Union Square': 17,
        'Financial District': 19,
        'Pacific Heights': 23,
        'Nob Hill': 20,
    }
}

# Define the current location and time
current_location = 'Embarcadero'
current_time = '9:00'

itinerary = []

# List of people with their constraints
people = [
    {'name': 'Kenneth', 'location': 'Richmond District', 'start': '21:15', 'end': '22:00', 'duration': 30},
    {'name': 'Lisa', 'location': 'Union Square', 'start': '9:00', 'end': '16:30', 'duration': 45},
    {'name': 'Joshua', 'location': 'Financial District', 'start': '12:00', 'end': '13:15', 'duration': 15},
    {'name': 'Nancy', 'location': 'Pacific Heights', 'start': '8:00', 'end': '11:30', 'duration': 90},
    {'name': 'Andrew', 'location': 'Nob Hill', 'start': '11:30', 'end': '20:15', 'duration': 60},
    {'name': 'John', 'location': 'Bayview', 'start': '16:45', 'end': '21:30', 'duration': 75},
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