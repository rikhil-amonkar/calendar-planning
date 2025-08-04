import json
from datetime import datetime, timedelta

# Define travel times
travel_times = {
    ('The Castro', 'Presidio'): 20, ('The Castro', 'Sunset District'): 17, ('The Castro', 'Haight-Ashbury'): 6,
    ('The Castro', 'Mission District'): 7, ('The Castro', 'Golden Gate Park'): 11, ('The Castro', 'Russian Hill'): 18,
    ('Presidio', 'The Castro'): 21, ('Presidio', 'Sunset District'): 15, ('Presidio', 'Haight-Ashbury'): 15,
    ('Presidio', 'Mission District'): 26, ('Presidio', 'Golden Gate Park'): 12, ('Presidio', 'Russian Hill'): 14,
    ('Sunset District', 'The Castro'): 17, ('Sunset District', 'Presidio'): 16, ('Sunset District', 'Haight-Ashbury'): 15,
    ('Sunset District', 'Mission District'): 24, ('Sunset District', 'Golden Gate Park'): 11, ('Sunset District', 'Russian Hill'): 24,
    ('Haight-Ashbury', 'The Castro'): 6, ('Haight-Ashbury', 'Presidio'): 15, ('Haight-Ashbury', 'Sunset District'): 15,
    ('Haight-Ashbury', 'Mission District'): 11, ('Haight-Ashbury', 'Golden Gate Park'): 7, ('Haight-Ashbury', 'Russian Hill'): 17,
    ('Mission District', 'The Castro'): 7, ('Mission District', 'Presidio'): 25, ('Mission District', 'Sunset District'): 24,
    ('Mission District', 'Haight-Ashbury'): 12, ('Mission District', 'Golden Gate Park'): 17, ('Mission District', 'Russian Hill'): 15,
    ('Golden Gate Park', 'The Castro'): 13, ('Golden Gate Park', 'Presidio'): 11, ('Golden Gate Park', 'Sunset District'): 10,
    ('Golden Gate Park', 'Haight-Ashbury'): 7, ('Golden Gate Park', 'Mission District'): 17, ('Golden Gate Park', 'Russian Hill'): 19,
    ('Russian Hill', 'The Castro'): 21, ('Russian Hill', 'Presidio'): 14, ('Russian Hill', 'Sunset District'): 23,
    ('Russian Hill', 'Haight-Ashbury'): 17, ('Russian Hill', 'Mission District'): 16, ('Russian Hill', 'Golden Gate Park'): 21,
}

# Define meeting constraints
meetings = {
    'Rebecca': {'location': 'Presidio', 'start': '18:15', 'end': '20:45', 'min_duration': 60},
    'Linda': {'location': 'Sunset District', 'start': '15:30', 'end': '19:45', 'min_duration': 30},
    'Elizabeth': {'location': 'Haight-Ashbury', 'start': '17:15', 'end': '19:30', 'min_duration': 105},
    'William': {'location': 'Mission District', 'start': '13:15', 'end': '19:30', 'min_duration': 30},
    'Robert': {'location': 'Golden Gate Park', 'start': '14:15', 'end': '21:30', 'min_duration': 45},
    'Mark': {'location': 'Russian Hill', 'start': '10:00', 'end': '21:15', 'min_duration': 75},
}

def parse_time(time_str):
    return datetime.strptime(time_str, '%H:%M')

def format_time(time_obj):
    return time_obj.strftime('%H:%M')

def find_meeting_times(current_time, location, person_info):
    start = max(current_time, parse_time(person_info['start']))
    end = min(parse_time(person_info['end']), current_time + timedelta(minutes=person_info['min_duration']))
    if start < end:
        return start, end
    return None, None

def can_travel(current_time, current_location, next_location):
    travel_time = travel_times[(current_location, next_location)]
    return current_time + timedelta(minutes=travel_time)

def calculate_schedule(start_time, start_location):
    itinerary = []
    current_time = start_time
    current_location = start_location
    remaining_meetings = meetings.copy()

    while remaining_meetings:
        best_meeting = None
        best_start = None
        best_end = None
        best_travel_time = float('inf')

        for person, info in remaining_meetings.items():
            if info['location'] == current_location:
                start, end = find_meeting_times(current_time, current_location, info)
                if start and end:
                    best_meeting = person
                    best_start = start
                    best_end = end
                    break
            else:
                travel_time = can_travel(current_time, current_location, info['location'])
                start, end = find_meeting_times(travel_time, info['location'], info)
                if start and end:
                    if travel_time < best_travel_time:
                        best_meeting = person
                        best_start = start
                        best_end = end
                        best_travel_time = travel_time

        if best_meeting:
            if best_travel_time != float('inf'):
                itinerary.append({
                    "action": "travel",
                    "location": meetings[best_meeting]['location'],
                    "start_time": format_time(current_time),
                    "end_time": format_time(best_travel_time)
                })
                current_time = best_travel_time
                current_location = meetings[best_meeting]['location']
            itinerary.append({
                "action": "meet",
                "location": meetings[best_meeting]['location'],
                "person": best_meeting,
                "start_time": format_time(best_start),
                "end_time": format_time(best_end)
            })
            current_time = best_end
            del remaining_meetings[best_meeting]
        else:
            break

    return itinerary

start_time = parse_time('9:00')
start_location = 'The Castro'
itinerary = calculate_schedule(start_time, start_location)

print(json.dumps({"itinerary": itinerary}, indent=2))