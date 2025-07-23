import json
from datetime import datetime, timedelta

# Define the travel times
travel_times = {
    ('Marina District', 'Richmond District'): 11,
    ('Marina District', 'Union Square'): 16,
    ('Marina District', 'Nob Hill'): 12,
    ('Marina District', 'Fisherman\'s Wharf'): 10,
    ('Marina District', 'Golden Gate Park'): 18,
    ('Marina District', 'Embarcadero'): 14,
    ('Marina District', 'Financial District'): 17,
    ('Marina District', 'North Beach'): 11,
    ('Marina District', 'Presidio'): 10,
    ('Richmond District', 'Marina District'): 9,
    ('Richmond District', 'Union Square'): 21,
    ('Richmond District', 'Nob Hill'): 17,
    ('Richmond District', 'Fisherman\'s Wharf'): 18,
    ('Richmond District', 'Golden Gate Park'): 9,
    ('Richmond District', 'Embarcadero'): 19,
    ('Richmond District', 'Financial District'): 22,
    ('Richmond District', 'North Beach'): 17,
    ('Richmond District', 'Presidio'): 7,
    ('Union Square', 'Marina District'): 18,
    ('Union Square', 'Richmond District'): 20,
    ('Union Square', 'Nob Hill'): 9,
    ('Union Square', 'Fisherman\'s Wharf'): 15,
    ('Union Square', 'Golden Gate Park'): 22,
    ('Union Square', 'Embarcadero'): 11,
    ('Union Square', 'Financial District'): 9,
    ('Union Square', 'North Beach'): 10,
    ('Union Square', 'Presidio'): 24,
    ('Nob Hill', 'Marina District'): 11,
    ('Nob Hill', 'Richmond District'): 14,
    ('Nob Hill', 'Union Square'): 7,
    ('Nob Hill', 'Fisherman\'s Wharf'): 10,
    ('Nob Hill', 'Golden Gate Park'): 17,
    ('Nob Hill', 'Embarcadero'): 9,
    ('Nob Hill', 'Financial District'): 9,
    ('Nob Hill', 'North Beach'): 8,
    ('Nob Hill', 'Presidio'): 17,
    ('Fisherman\'s Wharf', 'Marina District'): 9,
    ('Fisherman\'s Wharf', 'Richmond District'): 18,
    ('Fisherman\'s Wharf', 'Union Square'): 13,
    ('Fisherman\'s Wharf', 'Nob Hill'): 11,
    ('Fisherman\'s Wharf', 'Golden Gate Park'): 25,
    ('Fisherman\'s Wharf', 'Embarcadero'): 8,
    ('Fisherman\'s Wharf', 'Financial District'): 11,
    ('Fisherman\'s Wharf', 'North Beach'): 6,
    ('Fisherman\'s Wharf', 'Presidio'): 17,
    ('Golden Gate Park', 'Marina District'): 16,
    ('Golden Gate Park', 'Richmond District'): 7,
    ('Golden Gate Park', 'Union Square'): 22,
    ('Golden Gate Park', 'Nob Hill'): 20,
    ('Golden Gate Park', 'Fisherman\'s Wharf'): 24,
    ('Golden Gate Park', 'Embarcadero'): 25,
    ('Golden Gate Park', 'Financial District'): 26,
    ('Golden Gate Park', 'North Beach'): 23,
    ('Golden Gate Park', 'Presidio'): 11,
    ('Embarcadero', 'Marina District'): 12,
    ('Embarcadero', 'Richmond District'): 21,
    ('Embarcadero', 'Union Square'): 10,
    ('Embarcadero', 'Nob Hill'): 10,
    ('Embarcadero', 'Fisherman\'s Wharf'): 6,
    ('Embarcadero', 'Golden Gate Park'): 25,
    ('Embarcadero', 'Financial District'): 5,
    ('Embarcadero', 'North Beach'): 5,
    ('Embarcadero', 'Presidio'): 20,
    ('Financial District', 'Marina District'): 15,
    ('Financial District', 'Richmond District'): 21,
    ('Financial District', 'Union Square'): 9,
    ('Financial District', 'Nob Hill'): 8,
    ('Financial District', 'Fisherman\'s Wharf'): 10,
    ('Financial District', 'Golden Gate Park'): 23,
    ('Financial District', 'Embarcadero'): 4,
    ('Financial District', 'North Beach'): 7,
    ('Financial District', 'Presidio'): 22,
    ('North Beach', 'Marina District'): 9,
    ('North Beach', 'Richmond District'): 18,
    ('North Beach', 'Union Square'): 7,
    ('North Beach', 'Nob Hill'): 7,
    ('North Beach', 'Fisherman\'s Wharf'): 5,
    ('North Beach', 'Golden Gate Park'): 22,
    ('North Beach', 'Embarcadero'): 6,
    ('North Beach', 'Financial District'): 8,
    ('North Beach', 'Presidio'): 17,
    ('Presidio', 'Marina District'): 11,
    ('Presidio', 'Richmond District'): 7,
    ('Presidio', 'Union Square'): 22,
    ('Presidio', 'Nob Hill'): 18,
    ('Presidio', 'Fisherman\'s Wharf'): 19,
    ('Presidio', 'Golden Gate Park'): 12,
    ('Presidio', 'Embarcadero'): 20,
    ('Presidio', 'Financial District'): 23,
    ('Presidio', 'North Beach'): 18,
}

# Define the meetings
meetings = {
    'Stephanie': {'location': 'Richmond District', 'start': '16:15', 'end': '21:30', 'min_duration': 75},
    'William': {'location': 'Union Square', 'start': '10:45', 'end': '17:30', 'min_duration': 45},
    'Elizabeth': {'location': 'Nob Hill', 'start': '12:15', 'end': '15:00', 'min_duration': 105},
    'Joseph': {'location': 'Fisherman\'s Wharf', 'start': '12:45', 'end': '14:00', 'min_duration': 75},
    'Anthony': {'location': 'Golden Gate Park', 'start': '13:00', 'end': '20:30', 'min_duration': 75},
    'Barbara': {'location': 'Embarcadero', 'start': '19:15', 'end': '20:30', 'min_duration': 75},
    'Carol': {'location': 'Financial District', 'start': '11:45', 'end': '16:15', 'min_duration': 60},
    'Sandra': {'location': 'North Beach', 'start': '10:00', 'end': '12:30', 'min_duration': 15},
    'Kenneth': {'location': 'Presidio', 'start': '21:15', 'end': '22:15', 'min_duration': 45},
}

# Convert time strings to datetime objects
def parse_time(time_str):
    return datetime.strptime(time_str, '%H:%M')

# Check if a meeting can fit within the available time
def can_meet(start, end, min_duration):
    duration = (end - start).total_seconds() / 60
    return duration >= min_duration

# Find the best meeting time within the available window
def find_best_meeting_time(location, start, end, min_duration, current_time):
    if can_meet(start, end, min_duration):
        return start, end
    return None, None

# Calculate the travel time between two locations
def get_travel_time(start_location, end_location):
    return travel_times.get((start_location, end_location), float('inf'))

# Main function to create the itinerary
def create_itinerary():
    current_time = parse_time('9:00')
    current_location = 'Marina District'
    itinerary = []

    # Sort meetings by start time
    sorted_meetings = sorted(meetings.items(), key=lambda x: parse_time(x[1]['start']))

    for person, details in sorted_meetings:
        location = details['location']
        start = parse_time(details['start'])
        end = parse_time(details['end'])
        min_duration = details['min_duration']

        # Calculate travel time to the next meeting location
        travel_time = get_travel_time(current_location, location)

        # Check if we can reach the meeting location on time
        arrival_time = current_time + timedelta(minutes=travel_time)

        # Find the best meeting time
        meeting_start, meeting_end = find_best_meeting_time(location, arrival_time, end, min_duration, current_time)

        if meeting_start and meeting_end:
            # Add travel action to itinerary
            itinerary.append({
                "action": "travel",
                "location": location,
                "start_time": current_time.strftime('%H:%M'),
                "end_time": arrival_time.strftime('%H:%M')
            })

            # Add meeting action to itinerary
            itinerary.append({
                "action": "meet",
                "location": location,
                "person": person,
                "start_time": meeting_start.strftime('%H:%M'),
                "end_time": meeting_end.strftime('%H:%M')
            })

            # Update current time and location
            current_time = meeting_end
            current_location = location

    return itinerary

# Generate the itinerary
itinerary = create_itinerary()

# Output the result as JSON
result = {"itinerary": itinerary}
print(json.dumps(result))