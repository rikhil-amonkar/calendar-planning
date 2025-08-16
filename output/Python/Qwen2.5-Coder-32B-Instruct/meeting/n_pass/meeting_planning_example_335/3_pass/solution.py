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

# Define meeting constraints
meetings = {
    'Helen': {'location': 'North Beach', 'start': '9:00', 'end': '17:00', 'min_duration': 15},
    'Betty': {'location': 'Financial District', 'start': '19:00', 'end': '21:45', 'min_duration': 90},
    'Amanda': {'location': 'Alamo Square', 'start': '19:45', 'end': '21:00', 'min_duration': 60},
    'Kevin': {'location': 'Mission District', 'start': '10:45', 'end': '14:45', 'min_duration': 45},
}

def parse_time(time_str):
    return datetime.strptime(time_str, '%H:%M')

def format_time(time_obj):
    return time_obj.strftime('%H:%M')

def can_meet(start, end, min_duration):
    duration = (end - start).total_seconds() / 60
    return duration >= min_duration

def find_meeting_schedule():
    current_location = 'Pacific Heights'
    current_time = parse_time('9:00')
    itinerary = []

    def add_meeting(person, location, start, end):
        nonlocal current_time
        if can_meet(start, end, meetings[person]['min_duration']):
            travel_time = travel_times.get((current_location, location), float('inf'))
            arrival_time = current_time + timedelta(minutes=travel_time)
            if arrival_time < start:
                arrival_time = start
            leave_time = arrival_time + timedelta(minutes=meetings[person]['min_duration'])
            if leave_time <= end:
                itinerary.append({
                    "action": "meet",
                    "location": location,
                    "person": person,
                    "start_time": format_time(arrival_time),
                    "end_time": format_time(leave_time)
                })
                current_time = leave_time
                return True
        return False

    # Sort meetings by their earliest possible start time
    sorted_meetings = sorted(meetings.items(), key=lambda x: parse_time(x[1]['start']))

    for person, details in sorted_meetings:
        location = details['location']
        start = parse_time(details['start'])
        end = parse_time(details['end'])
        if add_meeting(person, location, start, end):
            current_location = location

    return itinerary

itinerary = find_meeting_schedule()
result = {"itinerary": itinerary}
print(json.dumps(result))