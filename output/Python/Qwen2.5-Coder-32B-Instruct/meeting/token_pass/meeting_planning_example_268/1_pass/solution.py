import json
from datetime import datetime, timedelta

# Define travel times
travel_times = {
    ('Golden Gate Park', 'Alamo Square'): 10,
    ('Golden Gate Park', 'Presidio'): 11,
    ('Golden Gate Park', 'Russian Hill'): 19,
    ('Alamo Square', 'Golden Gate Park'): 9,
    ('Alamo Square', 'Presidio'): 18,
    ('Alamo Square', 'Russian Hill'): 13,
    ('Presidio', 'Golden Gate Park'): 12,
    ('Presidio', 'Alamo Square'): 18,
    ('Presidio', 'Russian Hill'): 14,
    ('Russian Hill', 'Golden Gate Park'): 21,
    ('Russian Hill', 'Alamo Square'): 15,
    ('Russian Hill', 'Presidio'): 14
}

# Define meeting constraints
meetings = {
    'Timothy': {'location': 'Alamo Square', 'start': '12:00', 'end': '16:15', 'min_duration': 105},
    'Mark': {'location': 'Presidio', 'start': '18:45', 'end': '21:00', 'min_duration': 60},
    'Joseph': {'location': 'Russian Hill', 'start': '16:45', 'end': '21:30', 'min_duration': 60}
}

def parse_time(time_str):
    return datetime.strptime(time_str, '%H:%M')

def time_diff(start, end):
    return (parse_time(end) - parse_time(start)).total_seconds() / 60

def can_meet(current_time, meeting_info):
    start = parse_time(meeting_info['start'])
    end = parse_time(meeting_info['end'])
    min_duration = meeting_info['min_duration']
    available_time = (end - start).total_seconds() / 60
    return current_time <= start and available_time >= min_duration

def backtrack(current_location, current_time, visited, itinerary):
    global best_itinerary

    # Check if this is the best itinerary found so far
    if len(visited) > len(best_itinerary):
        best_itinerary = visited.copy()

    # Try to meet each person
    for person, meeting_info in meetings.items():
        if person not in visited:
            location = meeting_info['location']
            if can_meet(current_time, meeting_info):
                travel_time = travel_times[(current_location, location)]
                meet_start = max(current_time + travel_time, parse_time(meeting_info['start']))
                meet_end = meet_start + timedelta(minutes=meeting_info['min_duration'])
                if meet_end <= parse_time(meeting_info['end']):
                    visited.append(person)
                    backtrack(location, meet_end, visited, itinerary + [{
                        "action": "meet",
                        "location": location,
                        "person": person,
                        "start_time": meet_start.strftime('%H:%M'),
                        "end_time": meet_end.strftime('%H:%M')
                    }])
                    visited.pop()

    # Explore other locations without meeting anyone
    for next_location in ['Golden Gate Park', 'Alamo Square', 'Presidio', 'Russian Hill']:
        if next_location != current_location:
            travel_time = travel_times[(current_location, next_location)]
            new_time = current_time + timedelta(minutes=travel_time)
            backtrack(next_location, new_time, visited, itinerary)

best_itinerary = []
backtrack('Golden Gate Park', parse_time('9:00'), [], [])

# Convert the best itinerary to the required JSON format
result = {
    "itinerary": best_itinerary
}

print(json.dumps(result, indent=2))