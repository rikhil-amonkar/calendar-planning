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
    ('Sunset District', 'Bayview'): 22,
}

# Define meeting constraints
constraints = {
    'Rebecca': {'location': 'Mission District', 'start': '11:30', 'end': '20:15', 'min_duration': 120},
    'Karen': {'location': 'Bayview', 'start': '12:45', 'end': '15:00', 'min_duration': 120},
    'Carol': {'location': 'Sunset District', 'start': '10:15', 'end': '11:45', 'min_duration': 30},
}

def parse_time(time_str):
    return datetime.strptime(time_str, '%H:%M')

def time_to_str(time_obj):
    return time_obj.strftime('%H:%M').lstrip('0')

def find_meeting_schedule():
    start_time = parse_time('9:00')
    current_location = 'Union Square'
    itinerary = []

    def add_meeting(person, location, start, end):
        itinerary.append({
            "action": "meet",
            "location": location,
            "person": person,
            "start_time": time_to_str(start),
            "end_time": time_to_str(end)
        })

    def can_meet(start, end, min_duration):
        duration = (end - start).seconds // 60
        return duration >= min_duration

    # Try to meet Carol first if possible
    carol_start = parse_time(constraints['Carol']['start'])
    carol_end = parse_time(constraints['Carol']['end'])
    travel_to_carol = travel_times[(current_location, constraints['Carol']['location'])]
    carol_meeting_start = start_time + timedelta(minutes=travel_to_carol)
    if carol_meeting_start < carol_start:
        carol_meeting_start = carol_start
    carol_meeting_end = carol_meeting_start + timedelta(minutes=constraints['Carol']['min_duration'])
    if carol_meeting_end <= carol_end:
        add_meeting('Carol', constraints['Carol']['location'], carol_meeting_start, carol_meeting_end)
        current_location = constraints['Carol']['location']
        start_time = carol_meeting_end

    # Try to meet Rebecca next if possible
    rebecca_start = parse_time(constraints['Rebecca']['start'])
    rebecca_end = parse_time(constraints['Rebecca']['end'])
    travel_to_rebecca = travel_times[(current_location, constraints['Rebecca']['location'])]
    rebecca_meeting_start = start_time + timedelta(minutes=travel_to_rebecca)
    if rebecca_meeting_start < rebecca_start:
        rebecca_meeting_start = rebecca_start
    rebecca_meeting_end = rebecca_meeting_start + timedelta(minutes=constraints['Rebecca']['min_duration'])
    if rebecca_meeting_end <= rebecca_end:
        add_meeting('Rebecca', constraints['Rebecca']['location'], rebecca_meeting_start, rebecca_meeting_end)
        current_location = constraints['Rebecca']['location']
        start_time = rebecca_meeting_end

    # Try to meet Karen last if possible
    karen_start = parse_time(constraints['Karen']['start'])
    karen_end = parse_time(constraints['Karen']['end'])
    travel_to_karen = travel_times[(current_location, constraints['Karen']['location'])]
    karen_meeting_start = start_time + timedelta(minutes=travel_to_karen)
    if karen_meeting_start < karen_start:
        karen_meeting_start = karen_start
    karen_meeting_end = karen_meeting_start + timedelta(minutes=constraints['Karen']['min_duration'])
    if karen_meeting_end <= karen_end:
        add_meeting('Karen', constraints['Karen']['location'], karen_meeting_start, karen_meeting_end)

    return itinerary

itinerary = find_meeting_schedule()
print(json.dumps({"itinerary": itinerary}))