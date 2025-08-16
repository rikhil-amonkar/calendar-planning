import json
from datetime import datetime, timedelta

# Define travel times
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
    ('Mission District', 'Alamo Square'): 11,
}

# Define constraints
constraints = {
    'Helen': {'location': 'North Beach', 'start': '9:00', 'end': '17:00', 'min_meet': 15},
    'Betty': {'location': 'Financial District', 'start': '19:00', 'end': '21:45', 'min_meet': 90},
    'Amanda': {'location': 'Alamo Square', 'start': '19:45', 'end': '21:00', 'min_meet': 60},
    'Kevin': {'location': 'Mission District', 'start': '10:45', 'end': '14:45', 'min_meet': 45},
}

# Convert time strings to datetime objects
def time_to_dt(time_str):
    return datetime.strptime(time_str, '%H:%M')

# Calculate the end time of a meeting
def calculate_end_time(start_time, duration):
    return start_time + timedelta(minutes=duration)

# Check if a meeting can happen within the person's availability
def can_meet(start_time, end_time, person_constraints):
    person_start = time_to_dt(person_constraints['start'])
    person_end = time_to_dt(person_constraints['end'])
    return start_time >= person_start and end_time <= person_end

# Find the optimal meeting schedule
def find_optimal_schedule():
    current_location = 'Pacific Heights'
    current_time = time_to_dt('9:00')
    itinerary = []

    # Sort constraints by start time
    sorted_constraints = sorted(constraints.items(), key=lambda x: time_to_dt(x[1]['start']))

    for person, person_constraints in sorted_constraints:
        location = person_constraints['location']
        min_meet = person_constraints['min_meet']

        # Calculate travel time
        travel_time = travel_times[(current_location, location)]

        # Calculate potential meeting start time
        potential_start_time = calculate_end_time(current_time, travel_time)

        # Calculate potential meeting end time
        potential_end_time = calculate_end_time(potential_start_time, min_meet)

        # Check if the meeting can happen within the person's availability
        while not can_meet(potential_start_time, potential_end_time, person_constraints):
            potential_start_time += timedelta(minutes=1)
            potential_end_time = calculate_end_time(potential_start_time, min_meet)
            if potential_end_time > time_to_dt(person_constraints['end']):
                break

        # If a valid meeting time is found, add it to the itinerary
        if can_meet(potential_start_time, potential_end_time, person_constraints):
            itinerary.append({
                "action": "meet",
                "location": location,
                "person": person,
                "start_time": potential_start_time.strftime('%H:%M'),
                "end_time": potential_end_time.strftime('%H:%M')
            })
            current_time = potential_end_time
            current_location = location

    return itinerary

# Generate the optimal schedule
optimal_schedule = find_optimal_schedule()

# Output the result as a JSON-formatted dictionary
print(json.dumps({"itinerary": optimal_schedule}, indent=2))