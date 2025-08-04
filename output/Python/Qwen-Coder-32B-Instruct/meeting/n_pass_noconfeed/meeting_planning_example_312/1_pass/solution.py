import json
from datetime import datetime, timedelta

# Define travel times
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
    ('Golden Gate Park', 'Mission District'): 17,
}

# Define meeting constraints
constraints = {
    'Sarah': {'location': 'Sunset District', 'start': '10:45', 'end': '19:00', 'min_duration': 30},
    'Richard': {'location': 'Haight-Ashbury', 'start': '11:45', 'end': '15:45', 'min_duration': 90},
    'Elizabeth': {'location': 'Mission District', 'start': '11:00', 'end': '17:15', 'min_duration': 120},
    'Michelle': {'location': 'Golden Gate Park', 'start': '18:15', 'end': '20:45', 'min_duration': 90},
}

def parse_time(time_str):
    return datetime.strptime(time_str, '%H:%M')

def time_to_str(dt):
    return dt.strftime('%H:%M')

def find_schedule(start_location, start_time):
    current_location = start_location
    current_time = parse_time(start_time)
    itinerary = []

    def add_meeting(person, location, start, end, min_duration):
        nonlocal current_time
        if current_time + timedelta(minutes=min_duration) <= parse_time(end):
            itinerary.append({
                "action": "meet",
                "location": location,
                "person": person,
                "start_time": time_to_str(current_time),
                "end_time": time_to_str(current_time + timedelta(minutes=min_duration))
            })
            current_time += timedelta(minutes=min_duration)

    # Try to meet Elizabeth first due to her long meeting time
    if current_time < parse_time(constraints['Elizabeth']['end']):
        add_meeting('Elizabeth', constraints['Elizabeth']['location'], constraints['Elizabeth']['start'], constraints['Elizabeth']['end'], constraints['Elizabeth']['min_duration'])

    # Try to meet Richard next
    if current_time < parse_time(constraints['Richard']['end']):
        travel_time = travel_times.get((current_location, constraints['Richard']['location']), float('inf'))
        if current_time + timedelta(minutes=travel_time) < parse_time(constraints['Richard']['end']):
            current_time += timedelta(minutes=travel_time)
            current_location = constraints['Richard']['location']
            add_meeting('Richard', constraints['Richard']['location'], constraints['Richard']['start'], constraints['Richard']['end'], constraints['Richard']['min_duration'])

    # Try to meet Sarah next
    if current_time < parse_time(constraints['Sarah']['end']):
        travel_time = travel_times.get((current_location, constraints['Sarah']['location']), float('inf'))
        if current_time + timedelta(minutes=travel_time) < parse_time(constraints['Sarah']['end']):
            current_time += timedelta(minutes=travel_time)
            current_location = constraints['Sarah']['location']
            add_meeting('Sarah', constraints['Sarah']['location'], constraints['Sarah']['start'], constraints['Sarah']['end'], constraints['Sarah']['min_duration'])

    # Try to meet Michelle last
    if current_time < parse_time(constraints['Michelle']['end']):
        travel_time = travel_times.get((current_location, constraints['Michelle']['location']), float('inf'))
        if current_time + timedelta(minutes=travel_time) < parse_time(constraints['Michelle']['end']):
            current_time += timedelta(minutes=travel_time)
            current_location = constraints['Michelle']['location']
            add_meeting('Michelle', constraints['Michelle']['location'], constraints['Michelle']['start'], constraints['Michelle']['end'], constraints['Michelle']['min_duration'])

    return itinerary

itinerary = find_schedule('Richmond District', '9:00')
print(json.dumps({"itinerary": itinerary}))