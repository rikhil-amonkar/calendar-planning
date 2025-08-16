import json
from datetime import datetime, timedelta

# Define the travel times between locations
travel_times = {
    ('Presidio', 'Richmond District'): 7,
    ('Presidio', 'North Beach'): 18,
    ('Presidio', 'Financial District'): 23,
    ('Presidio', 'Golden Gate Park'): 12,
    ('Presidio', 'Union Square'): 22,
    ('Richmond District', 'Presidio'): 7,
    ('Richmond District', 'North Beach'): 17,
    ('Richmond District', 'Financial District'): 22,
    ('Richmond District', 'Golden Gate Park'): 9,
    ('Richmond District', 'Union Square'): 21,
    ('North Beach', 'Presidio'): 17,
    ('North Beach', 'Richmond District'): 18,
    ('North Beach', 'Financial District'): 8,
    ('North Beach', 'Golden Gate Park'): 22,
    ('North Beach', 'Union Square'): 7,
    ('Financial District', 'Presidio'): 22,
    ('Financial District', 'Richmond District'): 21,
    ('Financial District', 'North Beach'): 7,
    ('Financial District', 'Golden Gate Park'): 23,
    ('Financial District', 'Union Square'): 9,
    ('Golden Gate Park', 'Presidio'): 11,
    ('Golden Gate Park', 'Richmond District'): 7,
    ('Golden Gate Park', 'North Beach'): 24,
    ('Golden Gate Park', 'Financial District'): 26,
    ('Golden Gate Park', 'Union Square'): 22,
    ('Union Square', 'Presidio'): 24,
    ('Union Square', 'Richmond District'): 20,
    ('Union Square', 'North Beach'): 10,
    ('Union Square', 'Financial District'): 9,
    ('Union Square', 'Golden Gate Park'): 22,
}

# Define the meeting constraints
constraints = {
    'Jason': {'location': 'Richmond District', 'start': '13:00', 'end': '20:45', 'min_duration': 90},
    'Melissa': {'location': 'North Beach', 'start': '18:45', 'end': '20:15', 'min_duration': 45},
    'Brian': {'location': 'Financial District', 'start': '09:45', 'end': '21:45', 'min_duration': 15},
    'Elizabeth': {'location': 'Golden Gate Park', 'start': '08:45', 'end': '21:30', 'min_duration': 105},
    'Laura': {'location': 'Union Square', 'start': '14:15', 'end': '19:30', 'min_duration': 75},
}

def parse_time(time_str):
    return datetime.strptime(time_str, '%H:%M')

def format_time(time_obj):
    return time_obj.strftime('%H:%M')

def can_meet(start, end, min_duration):
    return (end - start).total_seconds() / 60 >= min_duration

def find_optimal_schedule():
    start_time = parse_time('9:00')
    current_location = 'Presidio'
    itinerary = []

    # Sort constraints by start time
    sorted_constraints = sorted(constraints.items(), key=lambda x: parse_time(x[1]['start']))

    for person, details in sorted_constraints:
        location = details['location']
        start = parse_time(details['start'])
        end = parse_time(details['end'])
        min_duration = details['min_duration']

        # Calculate travel time to the next location
        travel_time = travel_times.get((current_location, location), float('inf'))

        # Calculate potential meeting start time
        potential_start = start_time + timedelta(minutes=travel_time)

        # Adjust potential start time if it's before the person's availability or after their end time minus min_duration
        if potential_start < start:
            potential_start = start
        elif potential_start > end - timedelta(minutes=min_duration):
            continue  # Skip this meeting if we can't fit it within the person's availability

        # Calculate potential meeting end time
        potential_end = potential_start + timedelta(minutes=min_duration)

        # Check if the meeting can fit within the person's availability
        if can_meet(potential_start, end, min_duration):
            # Add the meeting to the itinerary
            itinerary.append({
                "action": "meet",
                "location": location,
                "person": person,
                "start_time": format_time(potential_start),
                "end_time": format_time(potential_end)
            })

            # Update the current location and start time for the next meeting
            current_location = location
            start_time = potential_end

    return itinerary

optimal_schedule = find_optimal_schedule()
result = {"itinerary": optimal_schedule}
print(json.dumps(result))