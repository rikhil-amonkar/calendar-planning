# Read the input parameters and create a dictionary of travel times
travel_times = {
    'Golden Gate Park': {
        'Alamo Square': 10,
        'Presidio': 11,
        'Russian Hill': 19,
    },
    'Alamo Square': {
        'Golden Gate Park': 9,
        'Presidio': 18,
        'Russian Hill': 13,
    },
    'Presidio': {
        'Golden Gate Park': 12,
        'Alamo Square': 18,
        'Russian Hill': 14,
    },
    'Russian Hill': {
        'Golden Gate Park': 21,
        'Alamo Square': 15,
        'Presidio': 14,
    }
}

# Define the current location and time
current_location = 'Golden Gate Park'
current_time = '9:00'

itinerary = []

# List of people with their constraints
people = [
    {'name': 'Timothy', 'location': 'Alamo Square', 'start': '12:00', 'end': '16:15', 'duration': 105},
    {'name': 'Mark', 'location': 'Presidio', 'start': '20:45', 'end': '21:00', 'duration': 60},
    {'name': 'Joseph', 'location': 'Russian Hill', 'start': '16:45', 'end': '21:30', 'duration': 60},
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