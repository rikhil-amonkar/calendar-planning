import json
from datetime import datetime, timedelta

# Define travel times
travel_times = {
    ('Sunset District', 'Presidio'): 16, ('Sunset District', 'Nob Hill'): 27, ('Sunset District', 'Pacific Heights'): 21,
    ('Sunset District', 'Mission District'): 25, ('Sunset District', 'Marina District'): 21, ('Sunset District', 'North Beach'): 28,
    ('Sunset District', 'Russian Hill'): 24, ('Sunset District', 'Richmond District'): 12, ('Sunset District', 'Embarcadero'): 30,
    ('Sunset District', 'Alamo Square'): 17, ('Presidio', 'Sunset District'): 15, ('Presidio', 'Nob Hill'): 18,
    ('Presidio', 'Pacific Heights'): 11, ('Presidio', 'Mission District'): 26, ('Presidio', 'Marina District'): 11,
    ('Presidio', 'North Beach'): 18, ('Presidio', 'Russian Hill'): 14, ('Presidio', 'Richmond District'): 7,
    ('Presidio', 'Embarcadero'): 20, ('Presidio', 'Alamo Square'): 19, ('Nob Hill', 'Sunset District'): 24,
    ('Nob Hill', 'Presidio'): 17, ('Nob Hill', 'Pacific Heights'): 8, ('Nob Hill', 'Mission District'): 13,
    ('Nob Hill', 'Marina District'): 11, ('Nob Hill', 'North Beach'): 8, ('Nob Hill', 'Russian Hill'): 5,
    ('Nob Hill', 'Richmond District'): 14, ('Nob Hill', 'Embarcadero'): 9, ('Nob Hill', 'Alamo Square'): 11,
    ('Pacific Heights', 'Sunset District'): 21, ('Pacific Heights', 'Presidio'): 11, ('Pacific Heights', 'Nob Hill'): 8,
    ('Pacific Heights', 'Mission District'): 15, ('Pacific Heights', 'Marina District'): 6, ('Pacific Heights', 'North Beach'): 9,
    ('Pacific Heights', 'Russian Hill'): 7, ('Pacific Heights', 'Richmond District'): 12, ('Pacific Heights', 'Embarcadero'): 10,
    ('Pacific Heights', 'Alamo Square'): 10, ('Mission District', 'Sunset District'): 24, ('Mission District', 'Presidio'): 25,
    ('Mission District', 'Nob Hill'): 12, ('Mission District', 'Pacific Heights'): 16, ('Mission District', 'Marina District'): 19,
    ('Mission District', 'North Beach'): 17, ('Mission District', 'Russian Hill'): 15, ('Mission District', 'Richmond District'): 20,
    ('Mission District', 'Embarcadero'): 19, ('Mission District', 'Alamo Square'): 11, ('Marina District', 'Sunset District'): 19,
    ('Marina District', 'Presidio'): 10, ('Marina District', 'Nob Hill'): 12, ('Marina District', 'Pacific Heights'): 7,
    ('Marina District', 'Mission District'): 20, ('Marina District', 'North Beach'): 11, ('Marina District', 'Russian Hill'): 8,
    ('Marina District', 'Richmond District'): 11, ('Marina District', 'Embarcadero'): 14, ('Marina District', 'Alamo Square'): 15,
    ('North Beach', 'Sunset District'): 27, ('North Beach', 'Presidio'): 17, ('North Beach', 'Nob Hill'): 7,
    ('North Beach', 'Pacific Heights'): 8, ('North Beach', 'Mission District'): 18, ('North Beach', 'Marina District'): 9,
    ('North Beach', 'Russian Hill'): 4, ('North Beach', 'Richmond District'): 18, ('North Beach', 'Embarcadero'): 6,
    ('North Beach', 'Alamo Square'): 16, ('Russian Hill', 'Sunset District'): 23, ('Russian Hill', 'Presidio'): 14,
    ('Russian Hill', 'Nob Hill'): 5, ('Russian Hill', 'Pacific Heights'): 7, ('Russian Hill', 'Mission District'): 16,
    ('Russian Hill', 'Marina District'): 7, ('Russian Hill', 'North Beach'): 5, ('Russian Hill', 'Richmond District'): 14,
    ('Russian Hill', 'Embarcadero'): 8, ('Russian Hill', 'Alamo Square'): 15, ('Richmond District', 'Sunset District'): 11,
    ('Richmond District', 'Presidio'): 7, ('Richmond District', 'Nob Hill'): 17, ('Richmond District', 'Pacific Heights'): 10,
    ('Richmond District', 'Mission District'): 20, ('Richmond District', 'Marina District'): 9, ('Richmond District', 'North Beach'): 17,
    ('Richmond District', 'Russian Hill'): 13, ('Richmond District', 'Embarcadero'): 19, ('Richmond District', 'Alamo Square'): 13,
    ('Embarcadero', 'Sunset District'): 30, ('Embarcadero', 'Presidio'): 20, ('Embarcadero', 'Nob Hill'): 10,
    ('Embarcadero', 'Pacific Heights'): 11, ('Embarcadero', 'Mission District'): 20, ('Embarcadero', 'Marina District'): 12,
    ('Embarcadero', 'North Beach'): 5, ('Embarcadero', 'Russian Hill'): 8, ('Embarcadero', 'Richmond District'): 21,
    ('Embarcadero', 'Alamo Square'): 19, ('Alamo Square', 'Sunset District'): 16, ('Alamo Square', 'Presidio'): 17,
    ('Alamo Square', 'Nob Hill'): 11, ('Alamo Square', 'Pacific Heights'): 10, ('Alamo Square', 'Mission District'): 10,
    ('Alamo Square', 'Marina District'): 15, ('Alamo Square', 'North Beach'): 15, ('Alamo Square', 'Russian Hill'): 13,
    ('Alamo Square', 'Richmond District'): 11, ('Alamo Square', 'Embarcadero'): 16
}

# Define meeting constraints
meetings = {
    'Charles': {'location': 'Presidio', 'start': '13:15', 'end': '15:00', 'min_duration': 105},
    'Robert': {'location': 'Nob Hill', 'start': '13:15', 'end': '17:30', 'min_duration': 90},
    'Nancy': {'location': 'Pacific Heights', 'start': '14:45', 'end': '22:00', 'min_duration': 105},
    'Brian': {'location': 'Mission District', 'start': '15:30', 'end': '22:00', 'min_duration': 60},
    'Kimberly': {'location': 'Marina District', 'start': '17:00', 'end': '19:45', 'min_duration': 75},
    'David': {'location': 'North Beach', 'start': '14:45', 'end': '16:30', 'min_duration': 75},
    'William': {'location': 'Russian Hill', 'start': '12:30', 'end': '19:15', 'min_duration': 120},
    'Jeffrey': {'location': 'Richmond District', 'start': '12:00', 'end': '19:15', 'min_duration': 45},
    'Karen': {'location': 'Embarcadero', 'start': '14:15', 'end': '20:45', 'min_duration': 60},
    'Joshua': {'location': 'Alamo Square', 'start': '18:45', 'end': '22:00', 'min_duration': 60}
}

def time_to_minutes(time_str):
    return int(time_str[:2]) * 60 + int(time_str[3:])

def minutes_to_time(minutes):
    hours, minutes = divmod(minutes, 60)
    return f"{hours}:{minutes:02}"

def find_meeting_schedule(start_location, start_time, meetings, travel_times):
    def can_meet(meeting, current_time):
        meeting_start = time_to_minutes(meeting['start'])
        meeting_end = time_to_minutes(meeting['end'])
        return meeting_start <= current_time < meeting_end

    def get_available_meetings(current_time, current_location):
        available = []
        for person, details in meetings.items():
            if can_meet(details, current_time) and details['location'] != current_location:
                available.append((person, details))
        return available

    def find_best_meeting(current_time, current_location, visited):
        available_meetings = get_available_meetings(current_time, current_location)
        best_meeting = None
        best_score = -1
        for person, details in available_meetings:
            if person not in visited:
                travel_time = travel_times[(current_location, details['location'])]
                meeting_start = max(current_time + travel_time, time_to_minutes(details['start']))
                meeting_end = min(meeting_start + details['min_duration'], time_to_minutes(details['end']))
                if meeting_start < meeting_end:
                    score = meeting_end - meeting_start
                    if score > best_score:
                        best_score = score
                        best_meeting = (person, details, meeting_start, meeting_end)
        return best_meeting

    itinerary = []
    current_time = time_to_minutes(start_time)
    current_location = start_location
    visited = set()

    while True:
        best_meeting = find_best_meeting(current_time, current_location, visited)
        if not best_meeting:
            break
        person, details, meeting_start, meeting_end = best_meeting
        itinerary.append({
            "action": "meet",
            "location": details['location'],
            "person": person,
            "start_time": minutes_to_time(meeting_start),
            "end_time": minutes_to_time(meeting_end)
        })
        current_time = meeting_end
        current_location = details['location']
        visited.add(person)

    return itinerary

start_location = 'Sunset District'
start_time = '9:00'
itinerary = find_meeting_schedule(start_location, start_time, meetings, travel_times)

print(json.dumps({"itinerary": itinerary}))