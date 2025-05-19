# Read the input parameters and create a dictionary of travel times
travel_times = {
    'Nob Hill': {
        'Presidio': 17,
        'North Beach': 8,
        'Fisherman\'s Wharf': 11,
        'Pacific Heights': 8,
    },
    'Presidio': {
        'Nob Hill': 18,
        'North Beach': 18,
        'Fisherman\'s Wharf': 19,
        'Pacific Heights': 11,
    },
    'North Beach': {
        'Nob Hill': 7,
        'Presidio': 17,
        'Fisherman\'s Wharf': 5,
        'Pacific Heights': 8,
    },
    'Fisherman\'s Wharf': {
        'Nob Hill': 11,
        'Presidio': 17,
        'North Beach': 6,
        'Pacific Heights': 12,
    },
    'Pacific Heights': {
        'Nob Hill': 8,
        'Presidio': 11,
        'North Beach': 9,
        'Fisherman\'s Wharf': 13,
    }
}

# Define the current location and time
current_location = 'Nob Hill'
current_time = '9:00'

itinerary = []

# List of people with their constraints
people = [
    {'name': 'Jeffrey', 'location': 'Presidio', 'start': '8:00', 'end': '10:00', 'duration': 105},
    {'name': 'Steven', 'location': 'North Beach', 'start': '13:30', 'end': '22:00', 'duration': 45},
    {'name': 'Barbara', 'location': 'Fisherman\'s Wharf', 'start': '18:00', 'end': '21:30', 'duration': 30},
    {'name': 'John', 'location': 'Pacific Heights', 'start': '9:00', 'end': '13:30', 'duration': 15},
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