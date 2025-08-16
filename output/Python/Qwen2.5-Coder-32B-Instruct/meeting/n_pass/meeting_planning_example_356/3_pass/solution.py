import json
from datetime import datetime, timedelta

# Define travel times
travel_times = {
    ('Bayview', 'North Beach'): 21,
    ('Bayview', 'Presidio'): 31,
    ('Bayview', 'Haight-Ashbury'): 19,
    ('Bayview', 'Union Square'): 17,
    ('North Beach', 'Bayview'): 22,
    ('North Beach', 'Presidio'): 17,
    ('North Beach', 'Haight-Ashbury'): 18,
    ('North Beach', 'Union Square'): 7,
    ('Presidio', 'Bayview'): 31,
    ('Presidio', 'North Beach'): 18,
    ('Presidio', 'Haight-Ashbury'): 15,
    ('Presidio', 'Union Square'): 22,
    ('Haight-Ashbury', 'Bayview'): 18,
    ('Haight-Ashbury', 'North Beach'): 19,
    ('Haight-Ashbury', 'Presidio'): 15,
    ('Haight-Ashbury', 'Union Square'): 17,
    ('Union Square', 'Bayview'): 15,
    ('Union Square', 'North Beach'): 10,
    ('Union Square', 'Presidio'): 24,
    ('Union Square', 'Haight-Ashbury'): 18,
}

# Define meeting constraints
meetings = {
    'Barbara': {'location': 'North Beach', 'start': '13:45', 'end': '14:45', 'min_duration': 60},
    'Margaret': {'location': 'Presidio', 'start': '10:15', 'end': '15:15', 'min_duration': 30},
    'Kevin': {'location': 'Haight-Ashbury', 'start': '20:00', 'end': '20:30', 'min_duration': 30},
}

def parse_time(time_str):
    return datetime.strptime(time_str, '%H:%M')

def add_minutes(time_obj, minutes):
    return time_obj + timedelta(minutes=minutes)

def can_meet(start, end, min_duration):
    return (parse_time(end) - parse_time(start)).total_seconds() / 60 >= min_duration

def find_schedule():
    current_time = parse_time('9:00')
    current_location = 'Bayview'
    itinerary = []

    def try_meeting(person, location, start, end, min_duration):
        nonlocal current_time, current_location
        travel_time = travel_times.get((current_location, location), float('inf'))
        if travel_time == float('inf'):
            return False
        arrival_time = add_minutes(current_time, travel_time)
        meeting_start = max(arrival_time, parse_time(start))
        meeting_end = min(add_minutes(meeting_start, min_duration), parse_time(end))
        if meeting_start < meeting_end and can_meet(meeting_start.strftime('%H:%M'), meeting_end.strftime('%H:%M'), min_duration):
            itinerary.append({
                "action": "meet",
                "location": location,
                "person": person,
                "start_time": meeting_start.strftime('%H:%M'),
                "end_time": meeting_end.strftime('%H:%M')
            })
            current_time = meeting_end
            current_location = location
            return True
        return False

    # Try to schedule meetings in order of their start times
    for person, details in sorted(meetings.items(), key=lambda x: x[1]['start']):
        try_meeting(person, details['location'], details['start'], details['end'], details['min_duration'])

    return itinerary

itinerary = find_schedule()
result = {"itinerary": itinerary}
print(json.dumps(result, indent=4))