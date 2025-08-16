import json
from datetime import datetime, timedelta

# Define the travel times between locations
travel_times = {
    ('Pacific Heights', 'North Beach'): 9,
    ('Pacific Heights', 'Financial District'): 13,
    ('Pacific Heights', 'Alamo Square'): 10,
    ('Pacific Heights', 'Mission District'): 15,
    ('North Beach', 'Pacific Heights'): 8,
    ('North Beach', 'Financial District'): 8,
    ('North Beach', 'Alamo Square'): 16,
    ('North Beach', 'Mission District'): 18,
    ('Financial District', 'Pacific Heights'): 13,
    ('Financial District', 'North Beach'): 7,
    ('Financial District', 'Alamo Square'): 17,
    ('Financial District', 'Mission District'): 17,
    ('Alamo Square', 'Pacific Heights'): 10,
    ('Alamo Square', 'North Beach'): 15,
    ('Alamo Square', 'Financial District'): 17,
    ('Alamo Square', 'Mission District'): 10,
    ('Mission District', 'Pacific Heights'): 16,
    ('Mission District', 'North Beach'): 17,
    ('Mission District', 'Financial District'): 17,
    ('Mission District', 'Alamo Square'): 11
}

# Define the meeting constraints
constraints = {
    'Helen': {'location': 'North Beach', 'start': '9:00', 'end': '17:00', 'min_duration': 15},
    'Betty': {'location': 'Financial District', 'start': '19:00', 'end': '21:45', 'min_duration': 90},
    'Amanda': {'location': 'Alamo Square', 'start': '19:45', 'end': '21:00', 'min_duration': 60},
    'Kevin': {'location': 'Mission District', 'start': '10:45', 'end': '14:45', 'min_duration': 45}
}

def parse_time(time_str):
    return datetime.strptime(time_str, '%H:%M')

def add_minutes(time, minutes):
    return time + timedelta(minutes=minutes)

def can_meet(start, end, duration):
    return (end - start).total_seconds() / 60 >= duration

def find_optimal_schedule():
    current_location = 'Pacific Heights'
    current_time = parse_time('9:00')
    itinerary = []

    # Sort constraints by start time
    sorted_constraints = sorted(constraints.items(), key=lambda x: parse_time(x[1]['start']))

    for person, details in sorted_constraints:
        location = details['location']
        start_time = parse_time(details['start'])
        end_time = parse_time(details['end'])
        min_duration = details['min_duration']

        # Calculate travel time to the next location
        travel_time = travel_times[(current_location, location)]

        # Check if we can reach the location on time
        arrival_time = add_minutes(current_time, travel_time)
        if arrival_time > start_time:
            # We are late, try to adjust
            if arrival_time + timedelta(minutes=min_duration) > end_time:
                continue  # Skip this meeting if we can't stay long enough

        # Adjust start time if we are early
        meeting_start = max(arrival_time, start_time)
        meeting_end = add_minutes(meeting_start, min_duration)

        # Add the meeting to the itinerary
        itinerary.append({
            "action": "meet",
            "location": location,
            "person": person,
            "start_time": meeting_start.strftime('%H:%M'),
            "end_time": meeting_end.strftime('%H:%M')
        })

        # Update current location and time
        current_location = location
        current_time = meeting_end

    return itinerary

# Compute the optimal schedule
optimal_schedule = find_optimal_schedule()

# Output the result as a JSON-formatted dictionary
print(json.dumps({"itinerary": optimal_schedule}, indent=2))