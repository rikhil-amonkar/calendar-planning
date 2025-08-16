import json
from datetime import datetime, timedelta

# Define travel times
travel_times = {
    ('The Castro', 'Alamo Square'): 8,
    ('The Castro', 'Union Square'): 19,
    ('The Castro', 'Chinatown'): 20,
    ('Alamo Square', 'The Castro'): 8,
    ('Alamo Square', 'Union Square'): 14,
    ('Alamo Square', 'Chinatown'): 16,
    ('Union Square', 'The Castro'): 19,
    ('Union Square', 'Alamo Square'): 15,
    ('Union Square', 'Chinatown'): 7,
    ('Chinatown', 'The Castro'): 22,
    ('Chinatown', 'Alamo Square'): 17,
    ('Chinatown', 'Union Square'): 7
}

# Define constraints
constraints = {
    'Emily': {'location': 'Alamo Square', 'start': '11:45', 'end': '15:15', 'min_duration': 105},
    'Barbara': {'location': 'Union Square', 'start': '16:45', 'end': '18:15', 'min_duration': 60},
    'William': {'location': 'Chinatown', 'start': '17:15', 'end': '19:00', 'min_duration': 105}
}

def parse_time(time_str):
    return datetime.strptime(time_str, '%H:%M')

def format_time(time_obj):
    return time_obj.strftime('%H:%M').lstrip('0')

def calculate_schedule(start_time):
    current_time = parse_time(start_time)
    itinerary = []

    def add_meeting(person, location, start, end, min_duration):
        nonlocal current_time
        if current_time < start:
            current_time = start
        meeting_end = current_time + timedelta(minutes=min_duration)
        if meeting_end <= end:
            itinerary.append({
                "action": "meet",
                "location": location,
                "person": person,
                "start_time": format_time(current_time),
                "end_time": format_time(meeting_end)
            })
            current_time = meeting_end

    # Sort constraints by start time
    sorted_constraints = sorted(constraints.items(), key=lambda x: parse_time(x[1]['start']))

    # Try to meet each friend
    for person, details in sorted_constraints:
        location = details['location']
        start = parse_time(details['start'])
        end = parse_time(details['end'])
        min_duration = details['min_duration']

        # Calculate travel time to the next location
        if itinerary:
            last_location = itinerary[-1]['location']
            travel_time = travel_times[(last_location, location)]
            current_time += timedelta(minutes=travel_time)

        # Add meeting if possible
        add_meeting(person, location, start, end, min_duration)

    return itinerary

start_time = '9:00'
itinerary = calculate_schedule(start_time)

# Output the result as a JSON-formatted dictionary
result = {"itinerary": itinerary}
print(json.dumps(result))