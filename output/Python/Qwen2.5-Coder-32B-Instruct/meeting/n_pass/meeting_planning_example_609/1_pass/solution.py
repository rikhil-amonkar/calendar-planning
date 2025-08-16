import json
from datetime import datetime, timedelta

# Define travel times
travel_times = {
    ("Chinatown", "Mission District"): 18,
    ("Chinatown", "Alamo Square"): 17,
    ("Chinatown", "Pacific Heights"): 10,
    ("Chinatown", "Union Square"): 7,
    ("Chinatown", "Golden Gate Park"): 23,
    ("Chinatown", "Sunset District"): 29,
    ("Chinatown", "Presidio"): 19,
    ("Mission District", "Chinatown"): 16,
    ("Mission District", "Alamo Square"): 11,
    ("Mission District", "Pacific Heights"): 16,
    ("Mission District", "Union Square"): 15,
    ("Mission District", "Golden Gate Park"): 17,
    ("Mission District", "Sunset District"): 24,
    ("Mission District", "Presidio"): 25,
    ("Alamo Square", "Chinatown"): 16,
    ("Alamo Square", "Mission District"): 10,
    ("Alamo Square", "Pacific Heights"): 10,
    ("Alamo Square", "Union Square"): 14,
    ("Alamo Square", "Golden Gate Park"): 9,
    ("Alamo Square", "Sunset District"): 16,
    ("Alamo Square", "Presidio"): 18,
    ("Pacific Heights", "Chinatown"): 11,
    ("Pacific Heights", "Mission District"): 15,
    ("Pacific Heights", "Alamo Square"): 10,
    ("Pacific Heights", "Union Square"): 12,
    ("Pacific Heights", "Golden Gate Park"): 15,
    ("Pacific Heights", "Sunset District"): 21,
    ("Pacific Heights", "Presidio"): 11,
    ("Union Square", "Chinatown"): 7,
    ("Union Square", "Mission District"): 14,
    ("Union Square", "Alamo Square"): 15,
    ("Union Square", "Pacific Heights"): 15,
    ("Union Square", "Golden Gate Park"): 22,
    ("Union Square", "Sunset District"): 26,
    ("Union Square", "Presidio"): 24,
    ("Golden Gate Park", "Chinatown"): 23,
    ("Golden Gate Park", "Mission District"): 17,
    ("Golden Gate Park", "Alamo Square"): 10,
    ("Golden Gate Park", "Pacific Heights"): 16,
    ("Golden Gate Park", "Union Square"): 22,
    ("Golden Gate Park", "Sunset District"): 10,
    ("Golden Gate Park", "Presidio"): 11,
    ("Sunset District", "Chinatown"): 30,
    ("Sunset District", "Mission District"): 24,
    ("Sunset District", "Alamo Square"): 17,
    ("Sunset District", "Pacific Heights"): 21,
    ("Sunset District", "Union Square"): 30,
    ("Sunset District", "Golden Gate Park"): 11,
    ("Sunset District", "Presidio"): 16,
    ("Presidio", "Chinatown"): 21,
    ("Presidio", "Mission District"): 26,
    ("Presidio", "Alamo Square"): 18,
    ("Presidio", "Pacific Heights"): 11,
    ("Presidio", "Union Square"): 22,
    ("Presidio", "Golden Gate Park"): 12,
    ("Presidio", "Sunset District"): 15,
}

# Define constraints
constraints = {
    "David": {"location": "Mission District", "start": "8:00", "end": "19:45", "min_duration": 45},
    "Kenneth": {"location": "Alamo Square", "start": "14:00", "end": "19:45", "min_duration": 120},
    "John": {"location": "Pacific Heights", "start": "17:00", "end": "20:00", "min_duration": 15},
    "Charles": {"location": "Union Square", "start": "21:45", "end": "22:45", "min_duration": 60},
    "Deborah": {"location": "Golden Gate Park", "start": "7:00", "end": "18:15", "min_duration": 90},
    "Karen": {"location": "Sunset District", "start": "17:45", "end": "21:15", "min_duration": 15},
    "Carol": {"location": "Presidio", "start": "8:15", "end": "9:15", "min_duration": 30},
}

# Convert times to datetime objects
def time_to_datetime(time_str):
    return datetime.strptime(time_str, "%H:%M")

def datetime_to_time(dt):
    return dt.strftime("%H:%M")

# Calculate travel time between two locations
def get_travel_time(start_loc, end_loc):
    return travel_times.get((start_loc, end_loc), float('inf'))

# Check if a meeting can fit within the available time
def can_meet(start_time, end_time, min_duration):
    return (end_time - start_time).total_seconds() / 60 >= min_duration

# Find the optimal schedule
def find_optimal_schedule(constraints, travel_times):
    current_location = "Chinatown"
    current_time = time_to_datetime("9:00")
    itinerary = []

    # Sort constraints by start time
    sorted_constraints = sorted(constraints.items(), key=lambda x: time_to_datetime(x[1]['start']))

    for name, constraint in sorted_constraints:
        location = constraint['location']
        start_time = time_to_datetime(constraint['start'])
        end_time = time_to_datetime(constraint['end'])
        min_duration = constraint['min_duration']

        # Calculate travel time to the next location
        travel_time = get_travel_time(current_location, location)

        # Calculate potential meeting start and end times
        potential_start_time = current_time + timedelta(minutes=travel_time)
        potential_end_time = potential_start_time + timedelta(minutes=min_duration)

        # Adjust meeting times if necessary
        if potential_start_time < start_time:
            potential_start_time = start_time
            potential_end_time = potential_start_time + timedelta(minutes=min_duration)

        if potential_end_time > end_time:
            continue

        # Add meeting to itinerary if it fits within the constraints
        if can_meet(potential_start_time, end_time, min_duration):
            itinerary.append({
                "action": "meet",
                "location": location,
                "person": name,
                "start_time": datetime_to_time(potential_start_time),
                "end_time": datetime_to_time(potential_end_time)
            })
            current_location = location
            current_time = potential_end_time

    return itinerary

# Generate the optimal schedule
optimal_itinerary = find_optimal_schedule(constraints, travel_times)

# Output the result as JSON
print(json.dumps({"itinerary": optimal_itinerary}, indent=2))