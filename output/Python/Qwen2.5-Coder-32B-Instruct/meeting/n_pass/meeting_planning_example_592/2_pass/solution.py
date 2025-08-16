import json
from datetime import datetime, timedelta

# Define travel times
travel_times = {
    ('North Beach', 'Pacific Heights'): 8,
    ('North Beach', 'Chinatown'): 6,
    ('North Beach', 'Union Square'): 7,
    ('North Beach', 'Mission District'): 18,
    ('North Beach', 'Golden Gate Park'): 22,
    ('North Beach', 'Nob Hill'): 7,
    ('Pacific Heights', 'North Beach'): 9,
    ('Pacific Heights', 'Chinatown'): 11,
    ('Pacific Heights', 'Union Square'): 12,
    ('Pacific Heights', 'Mission District'): 15,
    ('Pacific Heights', 'Golden Gate Park'): 15,
    ('Pacific Heights', 'Nob Hill'): 8,
    ('Chinatown', 'North Beach'): 3,
    ('Chinatown', 'Pacific Heights'): 10,
    ('Chinatown', 'Union Square'): 7,
    ('Chinatown', 'Mission District'): 18,
    ('Chinatown', 'Golden Gate Park'): 23,
    ('Chinatown', 'Nob Hill'): 8,
    ('Union Square', 'North Beach'): 10,
    ('Union Square', 'Pacific Heights'): 15,
    ('Union Square', 'Chinatown'): 7,
    ('Union Square', 'Mission District'): 14,
    ('Union Square', 'Golden Gate Park'): 22,
    ('Union Square', 'Nob Hill'): 9,
    ('Mission District', 'North Beach'): 17,
    ('Mission District', 'Pacific Heights'): 16,
    ('Mission District', 'Chinatown'): 16,
    ('Mission District', 'Union Square'): 15,
    ('Mission District', 'Golden Gate Park'): 17,
    ('Mission District', 'Nob Hill'): 12,
    ('Golden Gate Park', 'North Beach'): 24,
    ('Golden Gate Park', 'Pacific Heights'): 16,
    ('Golden Gate Park', 'Chinatown'): 23,
    ('Golden Gate Park', 'Union Square'): 22,
    ('Golden Gate Park', 'Mission District'): 17,
    ('Golden Gate Park', 'Nob Hill'): 20,
    ('Nob Hill', 'North Beach'): 8,
    ('Nob Hill', 'Pacific Heights'): 8,
    ('Nob Hill', 'Chinatown'): 6,
    ('Nob Hill', 'Union Square'): 7,
    ('Nob Hill', 'Mission District'): 13,
    ('Nob Hill', 'Golden Gate Park'): 17,
}

# Define meeting constraints
meetings = {
    'James': {'location': 'Pacific Heights', 'start': '20:00', 'end': '22:00', 'duration': 120},
    'Robert': {'location': 'Chinatown', 'start': '12:15', 'end': '16:45', 'duration': 90},
    'Jeffrey': {'location': 'Union Square', 'start': '9:30', 'end': '15:30', 'duration': 120},
    'Carol': {'location': 'Mission District', 'start': '18:15', 'end': '21:15', 'duration': 15},
    'Mark': {'location': 'Golden Gate Park', 'start': '11:30', 'end': '17:45', 'duration': 15},
    'Sandra': {'location': 'Nob Hill', 'start': '8:00', 'end': '15:30', 'duration': 15},
}

def parse_time(time_str):
    return datetime.strptime(time_str, '%H:%M')

def format_time(time_obj):
    return time_obj.strftime('%H:%M')

def find_meeting_schedule():
    current_location = 'North Beach'
    current_time = parse_time('9:00')
    itinerary = []

    def can_meet(person, start_time, end_time, duration):
        person_start = parse_time(meetings[person]['start'])
        person_end = parse_time(meetings[person]['end'])
        available_start = max(start_time, person_start)
        available_end = min(end_time, person_end)
        return (available_end - available_start).total_seconds() / 60 >= duration

    def get_next_location(current_location, current_time):
        best_location = None
        best_time = parse_time('22:00')  # Initialize best_time as a datetime object
        for person, details in meetings.items():
            if not any(item['person'] == person for item in itinerary):
                location = details['location']
                duration = details['duration']
                start_time = current_time + timedelta(minutes=travel_times[(current_location, location)])
                end_time = start_time + timedelta(minutes=duration)
                if end_time <= parse_time('22:00') and can_meet(person, start_time, end_time, duration):
                    if end_time < best_time:
                        best_time = end_time
                        best_location = location
        return best_location, best_time

    while current_time < parse_time('22:00'):
        next_location, next_time = get_next_location(current_location, current_time)
        if next_location is None:
            break
        travel_duration = travel_times[(current_location, next_location)]
        travel_end_time = current_time + timedelta(minutes=travel_duration)
        meeting_duration = meetings[next_location]['duration']
        meeting_start_time = travel_end_time
        meeting_end_time = meeting_start_time + timedelta(minutes=meeting_duration)
        itinerary.append({
            "action": "meet",
            "location": next_location,
            "person": next_location.split()[0],
            "start_time": format_time(meeting_start_time),
            "end_time": format_time(meeting_end_time)
        })
        current_location = next_location
        current_time = meeting_end_time

    return itinerary

itinerary = find_meeting_schedule()
result = {"itinerary": itinerary}
print(json.dumps(result))