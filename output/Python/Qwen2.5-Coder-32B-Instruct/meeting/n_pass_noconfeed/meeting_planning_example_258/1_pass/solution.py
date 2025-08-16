import json
from datetime import datetime, timedelta

# Define the travel times between locations
travel_times = {
    ('Embarcadero', 'Presidio'): 20,
    ('Embarcadero', 'Richmond District'): 21,
    ('Embarcadero', 'Fisherman\'s Wharf'): 6,
    ('Presidio', 'Embarcadero'): 20,
    ('Presidio', 'Richmond District'): 7,
    ('Presidio', 'Fisherman\'s Wharf'): 19,
    ('Richmond District', 'Embarcadero'): 19,
    ('Richmond District', 'Presidio'): 7,
    ('Richmond District', 'Fisherman\'s Wharf'): 18,
    ('Fisherman\'s Wharf', 'Embarcadero'): 8,
    ('Fisherman\'s Wharf', 'Presidio'): 17,
    ('Fisherman\'s Wharf', 'Richmond District'): 18,
}

# Define the meeting constraints
meetings = {
    'Betty': {'location': 'Presidio', 'start': '10:15', 'end': '21:30', 'min_duration': 45},
    'David': {'location': 'Richmond District', 'start': '13:00', 'end': '20:15', 'min_duration': 90},
    'Barbara': {'location': 'Fisherman\'s Wharf', 'start': '9:15', 'end': '20:15', 'min_duration': 120},
}

# Convert time strings to datetime objects
def parse_time(time_str):
    return datetime.strptime(time_str, '%H:%M')

# Calculate the latest start time for a meeting to fit the required duration
def latest_start_time(meeting_start, min_duration):
    return parse_time(meeting_start) + timedelta(minutes=min_duration)

# Calculate the earliest end time for a meeting to fit the required duration
def earliest_end_time(meeting_end, min_duration):
    return parse_time(meeting_end) - timedelta(minutes=min_duration)

# Check if two time intervals overlap
def intervals_overlap(start1, end1, start2, end2):
    return start1 < end2 and start2 < end1

# Find the optimal meeting schedule
def find_optimal_schedule():
    current_location = 'Embarcadero'
    current_time = parse_time('9:00')
    itinerary = []

    # Sort meetings by their start time
    sorted_meetings = sorted(meetings.items(), key=lambda x: parse_time(x[1]['start']))

    for name, details in sorted_meetings:
        location = details['location']
        meeting_start = parse_time(details['start'])
        meeting_end = parse_time(details['end'])
        min_duration = details['min_duration']

        # Calculate the latest start time and earliest end time for this meeting
        latest_start = latest_start_time(details['start'], min_duration)
        earliest_end = earliest_end_time(details['end'], min_duration)

        # Find a feasible time to travel to the next meeting location
        travel_time = travel_times[(current_location, location)]
        arrival_time = current_time + timedelta(minutes=travel_time)

        # Adjust the arrival time if it's too early
        if arrival_time < meeting_start:
            arrival_time = meeting_start

        # Check if the meeting can fit within the available time
        if arrival_time + timedelta(minutes=min_duration) <= meeting_end:
            # Add the meeting to the itinerary
            itinerary.append({
                "action": "meet",
                "location": location,
                "person": name,
                "start_time": arrival_time.strftime('%H:%M'),
                "end_time": (arrival_time + timedelta(minutes=min_duration)).strftime('%H:%M')
            })

            # Update the current location and time
            current_location = location
            current_time = arrival_time + timedelta(minutes=min_duration)

    return itinerary

# Generate the optimal schedule and output it as JSON
optimal_schedule = find_optimal_schedule()
output = {"itinerary": optimal_schedule}
print(json.dumps(output))