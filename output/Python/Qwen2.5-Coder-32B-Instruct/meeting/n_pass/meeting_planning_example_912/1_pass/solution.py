import json
from datetime import datetime, timedelta

# Define travel times
travel_times = {
    ('Union Square', 'Presidio'): 24, ('Union Square', 'Alamo Square'): 15, ('Union Square', 'Marina District'): 18,
    ('Union Square', 'Financial District'): 9, ('Union Square', 'Nob Hill'): 9, ('Union Square', 'Sunset District'): 27,
    ('Union Square', 'Chinatown'): 7, ('Union Square', 'Russian Hill'): 13, ('Union Square', 'North Beach'): 10,
    ('Union Square', 'Haight-Ashbury'): 18, ('Presidio', 'Union Square'): 22, ('Presidio', 'Alamo Square'): 19,
    ('Presidio', 'Marina District'): 11, ('Presidio', 'Financial District'): 23, ('Presidio', 'Nob Hill'): 18,
    ('Presidio', 'Sunset District'): 15, ('Presidio', 'Chinatown'): 21, ('Presidio', 'Russian Hill'): 14,
    ('Presidio', 'North Beach'): 18, ('Presidio', 'Haight-Ashbury'): 15, ('Alamo Square', 'Union Square'): 14,
    ('Alamo Square', 'Presidio'): 17, ('Alamo Square', 'Marina District'): 15, ('Alamo Square', 'Financial District'): 17,
    ('Alamo Square', 'Nob Hill'): 11, ('Alamo Square', 'Sunset District'): 16, ('Alamo Square', 'Chinatown'): 15,
    ('Alamo Square', 'Russian Hill'): 13, ('Alamo Square', 'North Beach'): 15, ('Alamo Square', 'Haight-Ashbury'): 5,
    ('Marina District', 'Union Square'): 16, ('Marina District', 'Presidio'): 10, ('Marina District', 'Alamo Square'): 15,
    ('Marina District', 'Financial District'): 17, ('Marina District', 'Nob Hill'): 12, ('Marina District', 'Sunset District'): 19,
    ('Marina District', 'Chinatown'): 15, ('Marina District', 'Russian Hill'): 8, ('Marina District', 'North Beach'): 11,
    ('Marina District', 'Haight-Ashbury'): 16, ('Financial District', 'Union Square'): 9, ('Financial District', 'Presidio'): 22,
    ('Financial District', 'Alamo Square'): 17, ('Financial District', 'Marina District'): 15, ('Financial District', 'Nob Hill'): 8,
    ('Financial District', 'Sunset District'): 30, ('Financial District', 'Chinatown'): 5, ('Financial District', 'Russian Hill'): 11,
    ('Financial District', 'North Beach'): 7, ('Financial District', 'Haight-Ashbury'): 19, ('Nob Hill', 'Union Square'): 7,
    ('Nob Hill', 'Presidio'): 17, ('Nob Hill', 'Alamo Square'): 11, ('Nob Hill', 'Marina District'): 11,
    ('Nob Hill', 'Financial District'): 9, ('Nob Hill', 'Sunset District'): 24, ('Nob Hill', 'Chinatown'): 6,
    ('Nob Hill', 'Russian Hill'): 5, ('Nob Hill', 'North Beach'): 8, ('Nob Hill', 'Haight-Ashbury'): 13,
    ('Sunset District', 'Union Square'): 30, ('Sunset District', 'Presidio'): 16, ('Sunset District', 'Alamo Square'): 17,
    ('Sunset District', 'Marina District'): 21, ('Sunset District', 'Financial District'): 30, ('Sunset District', 'Nob Hill'): 27,
    ('Sunset District', 'Chinatown'): 29, ('Sunset District', 'Russian Hill'): 23, ('Sunset District', 'North Beach'): 28,
    ('Sunset District', 'Haight-Ashbury'): 15, ('Chinatown', 'Union Square'): 7, ('Chinatown', 'Presidio'): 19,
    ('Chinatown', 'Alamo Square'): 17, ('Chinatown', 'Marina District'): 12, ('Chinatown', 'Financial District'): 5,
    ('Chinatown', 'Nob Hill'): 9, ('Chinatown', 'Sunset District'): 29, ('Chinatown', 'Russian Hill'): 7,
    ('Chinatown', 'North Beach'): 3, ('Chinatown', 'Haight-Ashbury'): 19, ('Russian Hill', 'Union Square'): 10,
    ('Russian Hill', 'Presidio'): 14, ('Russian Hill', 'Alamo Square'): 15, ('Russian Hill', 'Marina District'): 7,
    ('Russian Hill', 'Financial District'): 11, ('Russian Hill', 'Nob Hill'): 5, ('Russian Hill', 'Sunset District'): 23,
    ('Russian Hill', 'Chinatown'): 9, ('Russian Hill', 'North Beach'): 5, ('Russian Hill', 'Haight-Ashbury'): 17,
    ('North Beach', 'Union Square'): 7, ('North Beach', 'Presidio'): 17, ('North Beach', 'Alamo Square'): 16,
    ('North Beach', 'Marina District'): 9, ('North Beach', 'Financial District'): 8, ('North Beach', 'Nob Hill'): 7,
    ('North Beach', 'Sunset District'): 27, ('North Beach', 'Chinatown'): 6, ('North Beach', 'Russian Hill'): 4,
    ('North Beach', 'Haight-Ashbury'): 18, ('Haight-Ashbury', 'Union Square'): 19, ('Haight-Ashbury', 'Presidio'): 15,
    ('Haight-Ashbury', 'Alamo Square'): 5, ('Haight-Ashbury', 'Marina District'): 17, ('Haight-Ashbury', 'Financial District'): 21,
    ('Haight-Ashbury', 'Nob Hill'): 15, ('Haight-Ashbury', 'Sunset District'): 15, ('Haight-Ashbury', 'Chinatown'): 19,
    ('Haight-Ashbury', 'Russian Hill'): 17, ('Haight-Ashbury', 'North Beach'): 19
}

# Define meeting constraints
meetings = {
    'Kimberly': {'location': 'Presidio', 'start': '15:30', 'end': '16:00', 'min_duration': 15},
    'Elizabeth': {'location': 'Alamo Square', 'start': '19:15', 'end': '20:15', 'min_duration': 15},
    'Joshua': {'location': 'Marina District', 'start': '10:30', 'end': '14:15', 'min_duration': 45},
    'Sandra': {'location': 'Financial District', 'start': '19:30', 'end': '20:15', 'min_duration': 45},
    'Kenneth': {'location': 'Nob Hill', 'start': '12:45', 'end': '21:45', 'min_duration': 30},
    'Betty': {'location': 'Sunset District', 'start': '14:00', 'end': '19:00', 'min_duration': 60},
    'Deborah': {'location': 'Chinatown', 'start': '17:15', 'end': '20:30', 'min_duration': 15},
    'Barbara': {'location': 'Russian Hill', 'start': '17:30', 'end': '21:15', 'min_duration': 120},
    'Steven': {'location': 'North Beach', 'start': '17:45', 'end': '20:45', 'min_duration': 90},
    'Daniel': {'location': 'Haight-Ashbury', 'start': '18:30', 'end': '18:45', 'min_duration': 15}
}

def parse_time(time_str):
    return datetime.strptime(time_str, '%H:%M')

def format_time(dt):
    return dt.strftime('%H:%M')

def find_meeting_schedule():
    current_time = parse_time('9:00')
    current_location = 'Union Square'
    itinerary = []

    def can_meet(person, start_time, end_time, min_duration):
        meeting_start = max(current_time, start_time)
        meeting_end = min(end_time, meeting_start + timedelta(minutes=min_duration))
        return meeting_end <= end_time and meeting_end - meeting_start >= timedelta(minutes=min_duration)

    def travel_to(location):
        nonlocal current_time, current_location
        travel_time = travel_times.get((current_location, location), float('inf'))
        if travel_time == float('inf'):
            return False
        current_time += timedelta(minutes=travel_time)
        current_location = location
        return True

    for person, details in meetings.items():
        location = details['location']
        start_time = parse_time(details['start'])
        end_time = parse_time(details['end'])
        min_duration = details['min_duration']

        if can_meet(person, start_time, end_time, min_duration):
            if current_location != location:
                if not travel_to(location):
                    continue
            meeting_start = max(current_time, start_time)
            meeting_end = meeting_start + timedelta(minutes=min_duration)
            itinerary.append({
                "action": "meet",
                "location": location,
                "person": person,
                "start_time": format_time(meeting_start),
                "end_time": format_time(meeting_end)
            })
            current_time = meeting_end

    return itinerary

itinerary = find_meeting_schedule()
result = {"itinerary": itinerary}
print(json.dumps(result))