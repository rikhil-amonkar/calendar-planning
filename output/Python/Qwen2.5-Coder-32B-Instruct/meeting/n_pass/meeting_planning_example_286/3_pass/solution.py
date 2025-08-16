import json
from datetime import datetime, timedelta

# Define travel times
travel_times = {
    ('Union Square', 'Mission District'): 14,
    ('Union Square', 'Bayview'): 15,
    ('Union Square', 'Sunset District'): 26,
    ('Mission District', 'Union Square'): 15,
    ('Mission District', 'Bayview'): 15,
    ('Mission District', 'Sunset District'): 24,
    ('Bayview', 'Union Square'): 17,
    ('Bayview', 'Mission District'): 13,
    ('Bayview', 'Sunset District'): 23,
    ('Sunset District', 'Union Square'): 30,
    ('Sunset District', 'Mission District'): 24,
    ('Sunset District', 'Bayview'): 22
}

# Define meeting constraints
meetings = {
    'Rebecca': {'location': 'Mission District', 'start': '11:30', 'end': '13:30', 'min_duration': 120},
    'Karen': {'location': 'Bayview', 'start': '12:45', 'end': '15:00', 'min_duration': 120},
    'Carol': {'location': 'Sunset District', 'start': '10:15', 'end': '11:45', 'min_duration': 30}
}

def parse_time(time_str):
    return datetime.strptime(time_str, '%H:%M')

def add_minutes(time, minutes):
    return time + timedelta(minutes=minutes)

def can_meet(start, end, min_duration):
    return (end - start).total_seconds() / 60 >= min_duration

def find_optimal_schedule():
    start_time = parse_time('9:00')
    current_location = 'Union Square'
    itinerary = []

    def try_meeting(person, location, start, end, min_duration):
        nonlocal start_time, current_location, itinerary
        travel_time = travel_times[(current_location, location)]
        arrival_time = add_minutes(start_time, travel_time)
        if arrival_time < start:
            arrival_time = start
        leave_time = add_minutes(arrival_time, min_duration)
        if leave_time <= end:
            itinerary.append({
                "action": "meet",
                "location": location,
                "person": person,
                "start_time": arrival_time.strftime('%H:%M'),
                "end_time": leave_time.strftime('%H:%M')
            })
            start_time = leave_time
            current_location = location
            return True
        return False

    # Sort meetings by start time to prioritize earlier meetings
    sorted_meetings = sorted(meetings.items(), key=lambda x: parse_time(x[1]['start']))

    for person, info in sorted_meetings:
        if not try_meeting(person, info['location'], parse_time(info['start']), parse_time(info['end']), info['min_duration']):
            continue

    return itinerary

optimal_schedule = find_optimal_schedule()
print(json.dumps({"itinerary": optimal_schedule}))