import json
from datetime import datetime, timedelta

# Define the travel times between locations
travel_times = {
    ('Fisherman\'s Wharf', 'Golden Gate Park'): 25,
    ('Fisherman\'s Wharf', 'Presidio'): 17,
    ('Fisherman\'s Wharf', 'Richmond District'): 18,
    ('Golden Gate Park', 'Fisherman\'s Wharf'): 24,
    ('Golden Gate Park', 'Presidio'): 11,
    ('Golden Gate Park', 'Richmond District'): 7,
    ('Presidio', 'Fisherman\'s Wharf'): 19,
    ('Presidio', 'Golden Gate Park'): 12,
    ('Presidio', 'Richmond District'): 7,
    ('Richmond District', 'Fisherman\'s Wharf'): 18,
    ('Richmond District', 'Golden Gate Park'): 9,
    ('Richmond District', 'Presidio'): 7,
}

# Define the meeting constraints
meetings = {
    'Melissa': {'location': 'Golden Gate Park', 'start': '8:30', 'end': '20:00', 'min_duration': 15},
    'Nancy': {'location': 'Presidio', 'start': '19:45', 'end': '22:00', 'min_duration': 105},
    'Emily': {'location': 'Richmond District', 'start': '16:45', 'end': '22:00', 'min_duration': 120},
}

# Convert time strings to datetime objects
def parse_time(time_str):
    return datetime.strptime(time_str, '%H:%M')

# Check if two time intervals overlap
def intervals_overlap(start1, end1, start2, end2):
    return start1 < end2 and start2 < end1

# Calculate the optimal meeting schedule
def calculate_schedule():
    current_location = 'Fisherman\'s Wharf'
    current_time = parse_time('9:00')
    itinerary = []

    # Sort meetings by start time
    sorted_meetings = sorted(meetings.items(), key=lambda x: parse_time(x[1]['start']))

    for person, details in sorted_meetings:
        location = details['location']
        start_time = parse_time(details['start'])
        end_time = parse_time(details['end'])
        min_duration = timedelta(minutes=details['min_duration'])

        # Calculate travel time to the next meeting location
        travel_time = travel_times[(current_location, location)]
        arrival_time = current_time + timedelta(minutes=travel_time)

        # Adjust arrival time if it's before the meeting starts
        if arrival_time < start_time:
            arrival_time = start_time

        # Calculate the latest possible start time to meet the minimum duration requirement
        latest_start_time = end_time - min_duration

        # If the arrival time is after the latest possible start time, skip this meeting
        if arrival_time > latest_start_time:
            continue

        # Schedule the meeting
        meeting_end_time = arrival_time + min_duration
        itinerary.append({
            "action": "meet",
            "location": location,
            "person": person,
            "start_time": arrival_time.strftime('%H:%M'),
            "end_time": meeting_end_time.strftime('%H:%M')
        })

        # Update current location and time
        current_location = location
        current_time = meeting_end_time

    return itinerary

# Generate the optimal schedule and output it as JSON
optimal_schedule = calculate_schedule()
output = {
    "itinerary": optimal_schedule
}
print(json.dumps(output))