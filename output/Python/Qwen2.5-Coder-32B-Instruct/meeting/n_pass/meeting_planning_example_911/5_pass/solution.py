import json
from datetime import datetime, timedelta

# Define the travel times
travel_times = {
    ('The Castro', 'North Beach'): 20, ('The Castro', 'Golden Gate Park'): 11,
    ('The Castro', 'Embarcadero'): 22, ('The Castro', 'Haight-Ashbury'): 6,
    ('The Castro', 'Richmond District'): 16, ('The Castro', 'Nob Hill'): 16,
    ('The Castro', 'Marina District'): 21, ('The Castro', 'Presidio'): 20,
    ('The Castro', 'Union Square'): 19, ('The Castro', 'Financial District'): 21,
    ('North Beach', 'The Castro'): 23, ('North Beach', 'Golden Gate Park'): 22,
    ('North Beach', 'Embarcadero'): 6, ('North Beach', 'Haight-Ashbury'): 18,
    ('North Beach', 'Richmond District'): 18, ('North Beach', 'Nob Hill'): 7,
    ('North Beach', 'Marina District'): 9, ('North Beach', 'Presidio'): 17,
    ('North Beach', 'Union Square'): 7, ('North Beach', 'Financial District'): 8,
    ('Golden Gate Park', 'The Castro'): 13, ('Golden Gate Park', 'North Beach'): 23,
    ('Golden Gate Park', 'Embarcadero'): 25, ('Golden Gate Park', 'Haight-Ashbury'): 7,
    ('Golden Gate Park', 'Richmond District'): 7, ('Golden Gate Park', 'Nob Hill'): 20,
    ('Golden Gate Park', 'Marina District'): 16, ('Golden Gate Park', 'Presidio'): 11,
    ('Golden Gate Park', 'Union Square'): 22, ('Golden Gate Park', 'Financial District'): 26,
    ('Embarcadero', 'The Castro'): 25, ('Embarcadero', 'North Beach'): 5,
    ('Embarcadero', 'Golden Gate Park'): 25, ('Embarcadero', 'Haight-Ashbury'): 21,
    ('Embarcadero', 'Richmond District'): 21, ('Embarcadero', 'Nob Hill'): 10,
    ('Embarcadero', 'Marina District'): 12, ('Embarcadero', 'Presidio'): 20,
    ('Embarcadero', 'Union Square'): 10, ('Embarcadero', 'Financial District'): 5,
    ('Haight-Ashbury', 'The Castro'): 6, ('Haight-Ashbury', 'North Beach'): 19,
    ('Haight-Ashbury', 'Golden Gate Park'): 7, ('Haight-Ashbury', 'Embarcadero'): 20,
    ('Haight-Ashbury', 'Richmond District'): 10, ('Haight-Ashbury', 'Nob Hill'): 15,
    ('Haight-Ashbury', 'Marina District'): 17, ('Haight-Ashbury', 'Presidio'): 15,
    ('Haight-Ashbury', 'Union Square'): 19, ('Haight-Ashbury', 'Financial District'): 21,
    ('Richmond District', 'The Castro'): 16, ('Richmond District', 'North Beach'): 17,
    ('Richmond District', 'Golden Gate Park'): 9, ('Richmond District', 'Embarcadero'): 19,
    ('Richmond District', 'Haight-Ashbury'): 10, ('Richmond District', 'Nob Hill'): 17,
    ('Richmond District', 'Marina District'): 9, ('Richmond District', 'Presidio'): 7,
    ('Richmond District', 'Union Square'): 21, ('Richmond District', 'Financial District'): 22,
    ('Nob Hill', 'The Castro'): 17, ('Nob Hill', 'North Beach'): 8,
    ('Nob Hill', 'Golden Gate Park'): 17, ('Nob Hill', 'Embarcadero'): 9,
    ('Nob Hill', 'Haight-Ashbury'): 13, ('Nob Hill', 'Richmond District'): 14,
    ('Nob Hill', 'Marina District'): 11, ('Nob Hill', 'Presidio'): 17,
    ('Nob Hill', 'Union Square'): 7, ('Nob Hill', 'Financial District'): 9,
    ('Marina District', 'The Castro'): 22, ('Marina District', 'North Beach'): 11,
    ('Marina District', 'Golden Gate Park'): 18, ('Marina District', 'Embarcadero'): 14,
    ('Marina District', 'Haight-Ashbury'): 16, ('Marina District', 'Richmond District'): 11,
    ('Marina District', 'Nob Hill'): 12, ('Marina District', 'Presidio'): 10,
    ('Marina District', 'Union Square'): 16, ('Marina District', 'Financial District'): 17,
    ('Presidio', 'The Castro'): 21, ('Presidio', 'North Beach'): 18,
    ('Presidio', 'Golden Gate Park'): 12, ('Presidio', 'Embarcadero'): 20,
    ('Presidio', 'Haight-Ashbury'): 15, ('Presidio', 'Richmond District'): 7,
    ('Presidio', 'Nob Hill'): 18, ('Presidio', 'Marina District'): 11,
    ('Presidio', 'Union Square'): 22, ('Presidio', 'Financial District'): 23,
    ('Union Square', 'The Castro'): 17, ('Union Square', 'North Beach'): 10,
    ('Union Square', 'Golden Gate Park'): 22, ('Union Square', 'Embarcadero'): 11,
    ('Union Square', 'Haight-Ashbury'): 18, ('Union Square', 'Richmond District'): 20,
    ('Union Square', 'Nob Hill'): 9, ('Union Square', 'Marina District'): 18,
    ('Union Square', 'Presidio'): 24, ('Union Square', 'Financial District'): 9,
    ('Financial District', 'The Castro'): 20, ('Financial District', 'North Beach'): 7,
    ('Financial District', 'Golden Gate Park'): 23, ('Financial District', 'Embarcadero'): 4,
    ('Financial District', 'Haight-Ashbury'): 19, ('Financial District', 'Richmond District'): 21,
    ('Financial District', 'Nob Hill'): 8, ('Financial District', 'Marina District'): 15,
    ('Financial District', 'Presidio'): 22, ('Financial District', 'Union Square'): 9,
}

# Define the meeting constraints
meetings = {
    'Steven': {'location': 'North Beach', 'start': '17:30', 'end': '20:30', 'min_duration': 15},
    'Sarah': {'location': 'Golden Gate Park', 'start': '17:00', 'end': '19:15', 'min_duration': 75},
    'Brian': {'location': 'Embarcadero', 'start': '14:15', 'end': '16:00', 'min_duration': 105},
    'Stephanie': {'location': 'Haight-Ashbury', 'start': '10:15', 'end': '12:15', 'min_duration': 75},
    'Melissa': {'location': 'Richmond District', 'start': '14:00', 'end': '19:30', 'min_duration': 30},
    'Nancy': {'location': 'Nob Hill', 'start': '08:15', 'end': '12:45', 'min_duration': 90},
    'David': {'location': 'Marina District', 'start': '11:15', 'end': '13:15', 'min_duration': 120},
    'James': {'location': 'Presidio', 'start': '15:00', 'end': '18:15', 'min_duration': 120},
    'Elizabeth': {'location': 'Union Square', 'start': '11:30', 'end': '21:00', 'min_duration': 60},
    'Robert': {'location': 'Financial District', 'start': '13:15', 'end': '15:15', 'min_duration': 45},
}

# Convert time strings to datetime objects for easier manipulation
def parse_time(time_str):
    return datetime.strptime(time_str, '%H:%M').time()

def time_to_str(time_obj):
    return time_obj.strftime('%H:%M')

def find_optimal_schedule(start_location, start_time):
    def can_meet(meeting, current_time):
        meeting_start = parse_time(meeting['start'])
        meeting_end = parse_time(meeting['end'])
        min_duration = timedelta(minutes=meeting['min_duration'])
        return meeting_start <= current_time <= meeting_end - min_duration

    def next_location(current_location, current_time, visited):
        options = []
        for person, meeting in meetings.items():
            if person not in visited and can_meet(meeting, current_time):
                travel_time = travel_times[(current_location, meeting['location'])]
                new_time = datetime.combine(datetime.today(), current_time) + timedelta(minutes=travel_time)
                new_time = new_time.time()
                if can_meet(meeting, new_time):
                    options.append((new_time, meeting['location'], person))
        return sorted(options, key=lambda x: x[0])

    itinerary = []
    current_location = start_location
    current_time = parse_time(start_time)
    visited = set()

    while True:
        options = next_location(current_location, current_time, visited)
        if not options:
            break
        next_time, next_loc, person = options[0]
        meeting = meetings[person]
        meeting_start = parse_time(meeting['start'])
        meeting_end = parse_time(meeting['end'])
        min_duration = timedelta(minutes=meeting['min_duration'])
        actual_start = max(next_time, meeting_start)
        actual_end = min(actual_start + min_duration, meeting_end)
        itinerary.append({
            "action": "meet",
            "location": next_loc,
            "person": person,
            "start_time": time_to_str(actual_start),
            "end_time": time_to_str(actual_end)
        })
        current_time = (datetime.combine(datetime.today(), actual_end) + timedelta(minutes=5)).time()  # Add a 5-minute buffer
        current_location = next_loc
        visited.add(person)

    return itinerary

optimal_itinerary = find_optimal_schedule('The Castro', '09:00')
print(json.dumps({"itinerary": optimal_itinerary}, indent=2))