import json
from datetime import datetime, timedelta

# Define travel times
travel_times = {
    ('Fisherman\'s Wharf', 'Bayview'): 26,
    ('Fisherman\'s Wharf', 'Golden Gate Park'): 25,
    ('Fisherman\'s Wharf', 'Nob Hill'): 11,
    ('Fisherman\'s Wharf', 'Marina District'): 9,
    ('Fisherman\'s Wharf', 'Embarcadero'): 8,
    ('Bayview', 'Fisherman\'s Wharf'): 25,
    ('Bayview', 'Golden Gate Park'): 22,
    ('Bayview', 'Nob Hill'): 20,
    ('Bayview', 'Marina District'): 25,
    ('Bayview', 'Embarcadero'): 19,
    ('Golden Gate Park', 'Fisherman\'s Wharf'): 24,
    ('Golden Gate Park', 'Bayview'): 23,
    ('Golden Gate Park', 'Nob Hill'): 20,
    ('Golden Gate Park', 'Marina District'): 16,
    ('Golden Gate Park', 'Embarcadero'): 25,
    ('Nob Hill', 'Fisherman\'s Wharf'): 11,
    ('Nob Hill', 'Bayview'): 19,
    ('Nob Hill', 'Golden Gate Park'): 17,
    ('Nob Hill', 'Marina District'): 11,
    ('Nob Hill', 'Embarcadero'): 9,
    ('Marina District', 'Fisherman\'s Wharf'): 10,
    ('Marina District', 'Bayview'): 27,
    ('Marina District', 'Golden Gate Park'): 18,
    ('Marina District', 'Nob Hill'): 12,
    ('Marina District', 'Embarcadero'): 14,
    ('Embarcadero', 'Fisherman\'s Wharf'): 6,
    ('Embarcadero', 'Bayview'): 21,
    ('Embarcadero', 'Golden Gate Park'): 25,
    ('Embarcadero', 'Nob Hill'): 10,
    ('Embarcadero', 'Marina District'): 12,
}

# Define meeting constraints
meetings = {
    'Thomas': {'location': 'Bayview', 'start': '15:30', 'end': '18:30', 'min_duration': 120},
    'Stephanie': {'location': 'Golden Gate Park', 'start': '18:30', 'end': '21:45', 'min_duration': 30},
    'Laura': {'location': 'Nob Hill', 'start': '8:45', 'end': '16:15', 'min_duration': 30},
    'Betty': {'location': 'Marina District', 'start': '18:45', 'end': '21:45', 'min_duration': 45},
    'Patricia': {'location': 'Embarcadero', 'start': '17:30', 'end': '22:00', 'min_duration': 45},
}

def parse_time(time_str):
    return datetime.strptime(time_str, '%H:%M')

def add_minutes(time, minutes):
    return time + timedelta(minutes=minutes)

def format_time(time):
    return time.strftime('%H:%M')

def can_meet(start, end, min_duration):
    return (parse_time(end) - parse_time(start)).total_seconds() / 60 >= min_duration

def find_optimal_schedule():
    current_location = 'Fisherman\'s Wharf'
    current_time = parse_time('9:00')
    itinerary = []

    # Sort meetings by start time
    sorted_meetings = sorted(meetings.items(), key=lambda x: parse_time(x[1]['start']))

    for person, details in sorted_meetings:
        location = details['location']
        start = details['start']
        end = details['end']
        min_duration = details['min_duration']

        # Calculate travel time to the next location
        travel_time = travel_times[(current_location, location)]

        # Check if we can reach the location in time
        arrival_time = add_minutes(current_time, travel_time)
        if arrival_time < parse_time(start):
            # We can reach in time, check if we can stay long enough
            if can_meet(format_time(arrival_time), end, min_duration):
                # Add to itinerary
                itinerary.append({
                    "action": "meet",
                    "location": location,
                    "person": person,
                    "start_time": format_time(arrival_time),
                    "end_time": format_time(add_minutes(arrival_time, min_duration))
                })
                # Update current time and location
                current_time = add_minutes(arrival_time, min_duration)
                current_location = location
            else:
                # If we can't stay long enough, skip this meeting
                continue
        elif arrival_time <= parse_time(end):
            # We arrive during the meeting window, check if we can stay long enough
            if can_meet(format_time(arrival_time), end, min_duration):
                # Add to itinerary
                itinerary.append({
                    "action": "meet",
                    "location": location,
                    "person": person,
                    "start_time": format_time(arrival_time),
                    "end_time": format_time(add_minutes(arrival_time, min_duration))
                })
                # Update current time and location
                current_time = add_minutes(arrival_time, min_duration)
                current_location = location
            else:
                # If we can't stay long enough, skip this meeting
                continue
        else:
            # We arrive too late for this meeting
            continue

    return itinerary

optimal_schedule = find_optimal_schedule()
output = {
    "itinerary": optimal_schedule
}

print(json.dumps(output))