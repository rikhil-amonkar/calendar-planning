import json
from datetime import datetime, timedelta

# Define the travel times between locations
travel_times = {
    ('Presidio', 'Golden Gate Park'): 12,
    ('Presidio', 'Bayview'): 31,
    ('Presidio', 'Chinatown'): 21,
    ('Presidio', 'North Beach'): 18,
    ('Presidio', 'Mission District'): 26,
    ('Golden Gate Park', 'Presidio'): 11,
    ('Golden Gate Park', 'Bayview'): 23,
    ('Golden Gate Park', 'Chinatown'): 23,
    ('Golden Gate Park', 'North Beach'): 24,
    ('Golden Gate Park', 'Mission District'): 17,
    ('Bayview', 'Presidio'): 31,
    ('Bayview', 'Golden Gate Park'): 22,
    ('Bayview', 'Chinatown'): 18,
    ('Bayview', 'North Beach'): 21,
    ('Bayview', 'Mission District'): 13,
    ('Chinatown', 'Presidio'): 19,
    ('Chinatown', 'Golden Gate Park'): 23,
    ('Chinatown', 'Bayview'): 22,
    ('Chinatown', 'North Beach'): 3,
    ('Chinatown', 'Mission District'): 18,
    ('North Beach', 'Presidio'): 17,
    ('North Beach', 'Golden Gate Park'): 22,
    ('North Beach', 'Bayview'): 22,
    ('North Beach', 'Chinatown'): 6,
    ('North Beach', 'Mission District'): 18,
    ('Mission District', 'Presidio'): 25,
    ('Mission District', 'Golden Gate Park'): 17,
    ('Mission District', 'Bayview'): 15,
    ('Mission District', 'Chinatown'): 16,
    ('Mission District', 'North Beach'): 17,
}

# Define the meeting constraints
meetings = {
    'Jessica': {'location': 'Golden Gate Park', 'start': '13:45', 'end': '15:00', 'min_duration': 30},
    'Ashley': {'location': 'Bayview', 'start': '17:15', 'end': '20:00', 'min_duration': 105},
    'Ronald': {'location': 'Chinatown', 'start': '07:15', 'end': '14:45', 'min_duration': 90},
    'William': {'location': 'North Beach', 'start': '13:15', 'end': '20:15', 'min_duration': 15},
    'Daniel': {'location': 'Mission District', 'start': '07:00', 'end': '11:15', 'min_duration': 105},
}

def parse_time(time_str):
    return datetime.strptime(time_str, '%H:%M')

def format_time(dt):
    return dt.strftime('%H:%M')

def find_meeting_times(meetings):
    meeting_times = []
    for person, details in meetings.items():
        start = parse_time(details['start'])
        end = parse_time(details['end'])
        min_duration = details['min_duration']
        meeting_times.append((start, end, min_duration, details['location'], person))
    return sorted(meeting_times)

def can_meet(current_time, start, end, duration):
    return current_time + timedelta(minutes=duration) <= end

def find_optimal_schedule(meeting_times):
    current_time = parse_time('09:00')
    location = 'Presidio'
    itinerary = []

    for start, end, min_duration, loc, person in meeting_times:
        travel_time = travel_times.get((location, loc), float('inf'))
        if current_time + timedelta(minutes=travel_time) + timedelta(minutes=min_duration) > end:
            continue

        # Move to the location
        current_time += timedelta(minutes=travel_time)
        location = loc

        # Ensure we meet within the person's available window
        meeting_start = max(current_time, start)
        meeting_end = meeting_start + timedelta(minutes=min_duration)
        if meeting_end > end:
            continue  # Skip if the meeting would end after the person's available time

        itinerary.append({
            "action": "meet",
            "location": loc,
            "person": person,
            "start_time": format_time(meeting_start),
            "end_time": format_time(meeting_end)
        })
        current_time = meeting_end

    return itinerary

meeting_times = find_meeting_times(meetings)
optimal_itinerary = find_optimal_schedule(meeting_times)

print(json.dumps({"itinerary": optimal_itinerary}, indent=2))