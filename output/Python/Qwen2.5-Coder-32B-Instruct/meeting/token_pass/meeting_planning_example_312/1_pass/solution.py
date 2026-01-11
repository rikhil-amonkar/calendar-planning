import json
from datetime import datetime, timedelta

# Define travel times between locations
travel_times = {
    ('Richmond District', 'Sunset District'): 11,
    ('Richmond District', 'Haight-Ashbury'): 10,
    ('Richmond District', 'Mission District'): 20,
    ('Richmond District', 'Golden Gate Park'): 9,
    ('Sunset District', 'Richmond District'): 12,
    ('Sunset District', 'Haight-Ashbury'): 15,
    ('Sunset District', 'Mission District'): 24,
    ('Sunset District', 'Golden Gate Park'): 11,
    ('Haight-Ashbury', 'Richmond District'): 10,
    ('Haight-Ashbury', 'Sunset District'): 15,
    ('Haight-Ashbury', 'Mission District'): 11,
    ('Haight-Ashbury', 'Golden Gate Park'): 7,
    ('Mission District', 'Richmond District'): 20,
    ('Mission District', 'Sunset District'): 24,
    ('Mission District', 'Haight-Ashbury'): 12,
    ('Mission District', 'Golden Gate Park'): 17,
    ('Golden Gate Park', 'Richmond District'): 7,
    ('Golden Gate Park', 'Sunset District'): 10,
    ('Golden Gate Park', 'Haight-Ashbury'): 7,
    ('Golden Gate Park', 'Mission District'): 17
}

# Define friends' constraints
friends_constraints = {
    'Sarah': {'location': 'Sunset District', 'start_time': '10:45', 'end_time': '19:00', 'duration': 30},
    'Richard': {'location': 'Haight-Ashbury', 'start_time': '11:45', 'end_time': '15:45', 'duration': 90},
    'Elizabeth': {'location': 'Mission District', 'start_time': '11:00', 'end_time': '17:15', 'duration': 120},
    'Michelle': {'location': 'Golden Gate Park', 'start_time': '18:15', 'end_time': '20:45', 'duration': 90}
}

def parse_time(time_str):
    return datetime.strptime(time_str, '%H:%M')

def format_time(time_obj):
    return time_obj.strftime('%H:%M')

def find_schedule(start_location, start_time):
    current_location = start_location
    current_time = parse_time(start_time)
    itinerary = []

    # Sort friends by required meeting duration in descending order
    sorted_friends = sorted(friends_constraints.items(), key=lambda x: -x[1]['duration'])

    for name, constraints in sorted_friends:
        location = constraints['location']
        start_availability = parse_time(constraints['start_time'])
        end_availability = parse_time(constraints['end_time'])
        required_duration = timedelta(minutes=constraints['duration'])

        # Calculate travel time to the friend's location
        travel_time = timedelta(minutes=travel_times[(current_location, location)])
        potential_start_time = current_time + travel_time

        # Check if we can meet within the friend's availability
        if potential_start_time + required_duration <= end_availability:
            if potential_start_time >= start_availability:
                # Schedule the meeting
                itinerary.append({
                    "action": "meet",
                    "location": location,
                    "person": name,
                    "start_time": format_time(potential_start_time),
                    "end_time": format_time(potential_start_time + required_duration)
                })
                current_time = potential_start_time + required_duration
                current_location = location
            else:
                # Adjust start time to the earliest possible within availability
                potential_start_time = start_availability
                if potential_start_time + required_duration <= end_availability:
                    itinerary.append({
                        "action": "meet",
                        "location": location,
                        "person": name,
                        "start_time": format_time(potential_start_time),
                        "end_time": format_time(potential_start_time + required_duration)
                    })
                    current_time = potential_start_time + required_duration
                    current_location = location

    return itinerary

# Generate the schedule
schedule = find_schedule('Richmond District', '9:00')
result = {"itinerary": schedule}

# Output the result as JSON
print(json.dumps(result, indent=2))