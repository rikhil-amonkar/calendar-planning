import json
from datetime import datetime, timedelta

# Define travel times
travel_times = {
    ('Fisherman\'s Wharf', 'Presidio'): 17,
    ('Fisherman\'s Wharf', 'Richmond District'): 18,
    ('Fisherman\'s Wharf', 'Financial District'): 11,
    ('Presidio', 'Fisherman\'s Wharf'): 19,
    ('Presidio', 'Richmond District'): 7,
    ('Presidio', 'Financial District'): 23,
    ('Richmond District', 'Fisherman\'s Wharf'): 18,
    ('Richmond District', 'Presidio'): 7,
    ('Richmond District', 'Financial District'): 22,
    ('Financial District', 'Fisherman\'s Wharf'): 10,
    ('Financial District', 'Presidio'): 22,
    ('Financial District', 'Richmond District'): 21
}

# Define meeting constraints
meetings = {
    'Emily': {'location': 'Presidio', 'start': '16:15', 'end': '21:00', 'min_duration': 105},
    'Joseph': {'location': 'Richmond District', 'start': '17:15', 'end': '22:00', 'min_duration': 120},
    'Melissa': {'location': 'Financial District', 'start': '15:45', 'end': '21:45', 'min_duration': 75}
}

# Convert times to datetime objects for easier manipulation
def convert_to_datetime(time_str):
    return datetime.strptime(time_str, '%H:%M')

# Function to find all possible meeting times for a person
def find_meeting_times(person, start_location, current_time):
    location = meetings[person]['location']
    start_time = convert_to_datetime(meetings[person]['start'])
    end_time = convert_to_datetime(meetings[person]['end'])
    min_duration = meetings[person]['min_duration']
    
    possible_meetings = []
    while current_time + timedelta(minutes=travel_times[(start_location, location)]) <= end_time:
        arrival_time = current_time + timedelta(minutes=travel_times[(start_location, location)])
        if arrival_time >= start_time:
            meeting_start = arrival_time
            meeting_end = meeting_start + timedelta(minutes=min_duration)
            if meeting_end <= end_time:
                possible_meetings.append({
                    'location': location,
                    'person': person,
                    'start_time': meeting_start.strftime('%H:%M'),
                    'end_time': meeting_end.strftime('%H:%M')
                })
                current_time = meeting_end
            else:
                break
        else:
            current_time += timedelta(minutes=1)
    return possible_meetings

# Function to generate all possible itineraries
def generate_itineraries(current_location, current_time, visited, itinerary):
    if len(visited) == len(meetings):
        return [itinerary]
    
    all_itineraries = []
    for person, details in meetings.items():
        if person not in visited:
            possible_meetings = find_meeting_times(person, current_location, current_time)
            for meeting in possible_meetings:
                new_itinerary = itinerary + [meeting]
                new_visited = visited | {person}
                next_location = details['location']
                next_time = convert_to_datetime(meeting['end_time'])
                all_itineraries.extend(generate_itineraries(next_location, next_time, new_visited, new_itinerary))
    return all_itineraries

# Start from Fisherman's Wharf at 9:00 AM
start_location = 'Fisherman\'s Wharf'
start_time = convert_to_datetime('9:00')
initial_itinerary = []

# Generate all possible itineraries
all_itineraries = generate_itineraries(start_location, start_time, set(), initial_itinerary)

# Find the optimal itinerary (maximize number of meetings)
optimal_itinerary = max(all_itineraries, key=len, default=[])

# Output the result as a JSON-formatted dictionary
result = {
    "itinerary": optimal_itinerary
}

print(json.dumps(result, indent=2))