import json
from datetime import datetime, timedelta

# Define the travel times between locations
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

# Define the meeting constraints
constraints = {
    'Ronald': {'location': 'Russian Hill', 'start': '13:45', 'end': '17:15', 'min_duration': 105},
    'Patricia': {'location': 'Sunset District', 'start': '9:15', 'end': '22:00', 'min_duration': 60},
    'Laura': {'location': 'North Beach', 'start': '12:30', 'end': '12:45', 'min_duration': 15},
    'Emily': {'location': 'The Castro', 'start': '16:15', 'end': '18:30', 'min_duration': 60},
    'Mary': {'location': 'Golden Gate Park', 'start': '15:00', 'end': '16:30', 'min_duration': 60},
}

def parse_time(time_str):
    return datetime.strptime(time_str, '%H:%M')

def format_time(dt):
    return dt.strftime('%H:%M')

def find_meeting_times(constraint, current_time):
    start = max(parse_time(constraint['start']), current_time)
    end = min(parse_time(constraint['end']), start + timedelta(minutes=constraint['min_duration']))
    if end <= start:
        return None
    return start, end

def calculate_schedule():
    current_time = parse_time('9:00')
    itinerary = []
    visited_locations = set()
    
    while current_time < parse_time('22:00'):
        next_meeting = None
        for person, constraint in constraints.items():
            if person in [entry['person'] for entry in itinerary]:
                continue
            location = constraint['location']
            if location in visited_locations:
                continue
            meeting_times = find_meeting_times(constraint, current_time)
            if meeting_times:
                travel_time = travel_times.get(('Financial District', location), float('inf'))
                if current_time + timedelta(minutes=travel_time) <= meeting_times[0]:
                    next_meeting = (person, constraint, travel_time, meeting_times)
                    break
        
        if next_meeting:
            person, constraint, travel_time, meeting_times = next_meeting
            start_time = current_time + timedelta(minutes=travel_time)
            end_time = meeting_times[1]
            itinerary.append({
                'action': 'meet',
                'location': constraint['location'],
                'person': person,
                'start_time': format_time(start_time),
                'end_time': format_time(end_time)
            })
            current_time = end_time
            visited_locations.add(constraint['location'])
        else:
            break
    
    return itinerary

itinerary = calculate_schedule()
result = {"itinerary": itinerary}
print(json.dumps(result))