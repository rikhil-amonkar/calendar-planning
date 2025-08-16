import json
from datetime import datetime, timedelta

# Define travel times
travel_times = {
    ('The Castro', 'Presidio'): 20, ('The Castro', 'Sunset District'): 17,
    ('The Castro', 'Haight-Ashbury'): 6, ('The Castro', 'Mission District'): 7,
    ('The Castro', 'Golden Gate Park'): 11, ('The Castro', 'Russian Hill'): 18,
    ('Presidio', 'The Castro'): 21, ('Presidio', 'Sunset District'): 15,
    ('Presidio', 'Haight-Ashbury'): 15, ('Presidio', 'Mission District'): 26,
    ('Presidio', 'Golden Gate Park'): 12, ('Presidio', 'Russian Hill'): 14,
    ('Sunset District', 'The Castro'): 17, ('Sunset District', 'Presidio'): 16,
    ('Sunset District', 'Haight-Ashbury'): 15, ('Sunset District', 'Mission District'): 24,
    ('Sunset District', 'Golden Gate Park'): 11, ('Sunset District', 'Russian Hill'): 24,
    ('Haight-Ashbury', 'The Castro'): 6, ('Haight-Ashbury', 'Presidio'): 15,
    ('Haight-Ashbury', 'Sunset District'): 15, ('Haight-Ashbury', 'Mission District'): 11,
    ('Haight-Ashbury', 'Golden Gate Park'): 7, ('Haight-Ashbury', 'Russian Hill'): 17,
    ('Mission District', 'The Castro'): 7, ('Mission District', 'Presidio'): 25,
    ('Mission District', 'Sunset District'): 24, ('Mission District', 'Haight-Ashbury'): 12,
    ('Mission District', 'Golden Gate Park'): 17, ('Mission District', 'Russian Hill'): 15,
    ('Golden Gate Park', 'The Castro'): 13, ('Golden Gate Park', 'Presidio'): 11,
    ('Golden Gate Park', 'Sunset District'): 10, ('Golden Gate Park', 'Haight-Ashbury'): 7,
    ('Golden Gate Park', 'Mission District'): 17, ('Golden Gate Park', 'Russian Hill'): 19,
    ('Russian Hill', 'The Castro'): 21, ('Russian Hill', 'Presidio'): 14,
    ('Russian Hill', 'Sunset District'): 23, ('Russian Hill', 'Haight-Ashbury'): 17,
    ('Russian Hill', 'Mission District'): 16, ('Russian Hill', 'Golden Gate Park'): 21
}

# Define meeting constraints
constraints = {
    'Rebecca': {'location': 'Presidio', 'start': '18:15', 'end': '20:45', 'min_duration': 60},
    'Linda': {'location': 'Sunset District', 'start': '15:30', 'end': '19:45', 'min_duration': 30},
    'Elizabeth': {'location': 'Haight-Ashbury', 'start': '17:15', 'end': '19:30', 'min_duration': 105},
    'William': {'location': 'Mission District', 'start': '13:15', 'end': '19:30', 'min_duration': 30},
    'Robert': {'location': 'Golden Gate Park', 'start': '14:15', 'end': '21:30', 'min_duration': 45},
    'Mark': {'location': 'Russian Hill', 'start': '10:00', 'end': '21:15', 'min_duration': 75}
}

def parse_time(time_str):
    return datetime.strptime(time_str, '%H:%M')

def add_minutes(time_obj, minutes):
    return time_obj + timedelta(minutes=minutes)

def can_meet(start_time, end_time, person_start, person_end, min_duration):
    available_start = max(start_time, person_start)
    available_end = min(end_time, person_end)
    return (available_end - available_start).total_seconds() / 60 >= min_duration

def find_meeting_schedule():
    current_time = parse_time('9:00')
    current_location = 'The Castro'
    itinerary = []

    def try_meeting(person, location, start, end, min_duration):
        nonlocal current_time, current_location
        travel_time = travel_times.get((current_location, location), float('inf'))
        if can_meet(add_minutes(current_time, travel_time), end, start, end, min_duration):
            meet_start = max(add_minutes(current_time, travel_time), start)
            meet_end = min(add_minutes(meet_start, min_duration), end)
            itinerary.append({
                "action": "meet",
                "location": location,
                "person": person,
                "start_time": meet_start.strftime('%H:%M'),
                "end_time": meet_end.strftime('%H:%M')
            })
            current_time = meet_end
            current_location = location

    # Sort constraints by start time to prioritize earlier meetings
    for person, details in sorted(constraints.items(), key=lambda x: parse_time(x[1]['start'])):
        try_meeting(person, details['location'], parse_time(details['start']), parse_time(details['end']), details['min_duration'])

    return {"itinerary": itinerary}

if __name__ == "__main__":
    schedule = find_meeting_schedule()
    print(json.dumps(schedule, indent=4))