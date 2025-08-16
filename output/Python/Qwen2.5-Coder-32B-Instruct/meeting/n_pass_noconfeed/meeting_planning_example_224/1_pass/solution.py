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
constraints = {
    'Melissa': {'location': 'Golden Gate Park', 'start': '8:30', 'end': '20:00', 'min_duration': 15},
    'Nancy': {'location': 'Presidio', 'start': '19:45', 'end': '22:00', 'min_duration': 105},
    'Emily': {'location': 'Richmond District', 'start': '16:45', 'end': '22:00', 'min_duration': 120},
}

# Convert time strings to datetime objects
def time_to_datetime(time_str):
    return datetime.strptime(time_str, '%H:%M')

# Calculate the end time of a meeting
def calculate_meeting_end(start_time, duration):
    return start_time + timedelta(minutes=duration)

# Check if a meeting can fit within the person's availability
def can_meet(start_time, duration, person_constraints):
    meeting_end = calculate_meeting_end(start_time, duration)
    return person_constraints['start'] <= start_time.strftime('%H:%M') < meeting_end.strftime('%H:%M') <= person_constraints['end']

# Find the optimal meeting schedule
def find_optimal_schedule():
    current_location = 'Fisherman\'s Wharf'
    current_time = time_to_datetime('9:00')
    itinerary = []

    # Sort constraints by latest possible start time minus minimum duration
    sorted_constraints = sorted(constraints.items(), key=lambda x: time_to_datetime(x[1]['end']) - timedelta(minutes=x[1]['min_duration']))

    for name, constraint in sorted_constraints:
        location = constraint['location']
        min_duration = constraint['min_duration']
        available_start = time_to_datetime(constraint['start'])
        available_end = time_to_datetime(constraint['end'])

        # Calculate travel time to the next location
        travel_time = travel_times[(current_location, location)]
        potential_start = current_time + timedelta(minutes=travel_time)

        # Adjust start time if necessary to fit within availability
        if potential_start < available_start:
            potential_start = available_start

        # Check if we can meet the person for the required duration
        if can_meet(potential_start, min_duration, constraint):
            meeting_end = calculate_meeting_end(potential_start, min_duration)
            itinerary.append({
                "action": "meet",
                "location": location,
                "person": name,
                "start_time": potential_start.strftime('%H:%M'),
                "end_time": meeting_end.strftime('%H:%M')
            })
            current_time = meeting_end
            current_location = location

    return itinerary

# Generate the JSON output
optimal_itinerary = find_optimal_schedule()
output = {"itinerary": optimal_itinerary}
print(json.dumps(output))