import json
from datetime import datetime, timedelta

# Define travel times
travel_times = {
    ('Financial District', 'Russian Hill'): 10,
    ('Financial District', 'Sunset District'): 31,
    ('Financial District', 'North Beach'): 7,
    ('Financial District', 'The Castro'): 23,
    ('Financial District', 'Golden Gate Park'): 23,
    ('Russian Hill', 'Financial District'): 11,
    ('Russian Hill', 'Sunset District'): 23,
    ('Russian Hill', 'North Beach'): 5,
    ('Russian Hill', 'The Castro'): 21,
    ('Russian Hill', 'Golden Gate Park'): 21,
    ('Sunset District', 'Financial District'): 30,
    ('Sunset District', 'Russian Hill'): 24,
    ('Sunset District', 'North Beach'): 29,
    ('Sunset District', 'The Castro'): 17,
    ('Sunset District', 'Golden Gate Park'): 11,
    ('North Beach', 'Financial District'): 8,
    ('North Beach', 'Russian Hill'): 4,
    ('North Beach', 'Sunset District'): 27,
    ('North Beach', 'The Castro'): 22,
    ('North Beach', 'Golden Gate Park'): 22,
    ('The Castro', 'Financial District'): 20,
    ('The Castro', 'Russian Hill'): 18,
    ('The Castro', 'Sunset District'): 17,
    ('The Castro', 'North Beach'): 20,
    ('The Castro', 'Golden Gate Park'): 11,
    ('Golden Gate Park', 'Financial District'): 26,
    ('Golden Gate Park', 'Russian Hill'): 19,
    ('Golden Gate Park', 'Sunset District'): 10,
    ('Golden Gate Park', 'North Beach'): 24,
    ('Golden Gate Park', 'The Castro'): 13,
}

# Define meeting constraints
meetings = {
    'Ronald': {'location': 'Russian Hill', 'start': '13:45', 'end': '17:15', 'min_duration': 105},
    'Patricia': {'location': 'Sunset District', 'start': '9:15', 'end': '22:00', 'min_duration': 60},
    'Laura': {'location': 'North Beach', 'start': '12:30', 'end': '12:45', 'min_duration': 15},
    'Emily': {'location': 'The Castro', 'start': '16:15', 'end': '18:30', 'min_duration': 60},
    'Mary': {'location': 'Golden Gate Park', 'start': '15:00', 'end': '16:30', 'min_duration': 60},
}

def parse_time(time_str):
    return datetime.strptime(time_str, '%H:%M')

def time_to_str(time_obj):
    return time_obj.strftime('%H:%M')

def can_meet(start, end, min_duration):
    return (parse_time(end) - parse_time(start)).total_seconds() / 60 >= min_duration

def find_schedule():
    current_location = 'Financial District'
    current_time = parse_time('9:00')
    itinerary = []

    # Sort meetings by start time
    sorted_meetings = sorted(meetings.items(), key=lambda x: parse_time(x[1]['start']))

    for name, details in sorted_meetings:
        location = details['location']
        start = details['start']
        end = details['end']
        min_duration = details['min_duration']

        travel_time = travel_times[(current_location, location)]
        arrival_time = current_time + timedelta(minutes=travel_time)

        if arrival_time < parse_time(start):
            # Wait until the meeting starts
            arrival_time = parse_time(start)

        if can_meet(time_to_str(arrival_time), end, min_duration):
            meeting_start = arrival_time
            meeting_end = meeting_start + timedelta(minutes=min_duration)
            itinerary.append({
                "action": "meet",
                "location": location,
                "person": name,
                "start_time": time_to_str(meeting_start),
                "end_time": time_to_str(meeting_end)
            })
            current_time = meeting_end
            current_location = location

    return itinerary

itinerary = find_schedule()
result = {"itinerary": itinerary}
print(json.dumps(result))