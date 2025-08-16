import json
from datetime import datetime, timedelta

# Define travel times
travel_times = {
    ('Presidio', 'Haight-Ashbury'): 15,
    ('Presidio', 'Nob Hill'): 18,
    ('Presidio', 'Russian Hill'): 14,
    ('Presidio', 'North Beach'): 18,
    ('Presidio', 'Chinatown'): 21,
    ('Presidio', 'Union Square'): 22,
    ('Presidio', 'Embarcadero'): 20,
    ('Presidio', 'Financial District'): 23,
    ('Presidio', 'Marina District'): 11,
    ('Haight-Ashbury', 'Presidio'): 15,
    ('Haight-Ashbury', 'Nob Hill'): 15,
    ('Haight-Ashbury', 'Russian Hill'): 17,
    ('Haight-Ashbury', 'North Beach'): 19,
    ('Haight-Ashbury', 'Chinatown'): 19,
    ('Haight-Ashbury', 'Union Square'): 19,
    ('Haight-Ashbury', 'Embarcadero'): 20,
    ('Haight-Ashbury', 'Financial District'): 21,
    ('Haight-Ashbury', 'Marina District'): 17,
    ('Nob Hill', 'Presidio'): 17,
    ('Nob Hill', 'Haight-Ashbury'): 13,
    ('Nob Hill', 'Russian Hill'): 5,
    ('Nob Hill', 'North Beach'): 8,
    ('Nob Hill', 'Chinatown'): 6,
    ('Nob Hill', 'Union Square'): 7,
    ('Nob Hill', 'Embarcadero'): 9,
    ('Nob Hill', 'Financial District'): 9,
    ('Nob Hill', 'Marina District'): 11,
    ('Russian Hill', 'Presidio'): 14,
    ('Russian Hill', 'Haight-Ashbury'): 17,
    ('Russian Hill', 'Nob Hill'): 5,
    ('Russian Hill', 'North Beach'): 5,
    ('Russian Hill', 'Chinatown'): 9,
    ('Russian Hill', 'Union Square'): 10,
    ('Russian Hill', 'Embarcadero'): 8,
    ('Russian Hill', 'Financial District'): 11,
    ('Russian Hill', 'Marina District'): 7,
    ('North Beach', 'Presidio'): 17,
    ('North Beach', 'Haight-Ashbury'): 18,
    ('North Beach', 'Nob Hill'): 7,
    ('North Beach', 'Russian Hill'): 4,
    ('North Beach', 'Chinatown'): 6,
    ('North Beach', 'Union Square'): 7,
    ('North Beach', 'Embarcadero'): 6,
    ('North Beach', 'Financial District'): 8,
    ('North Beach', 'Marina District'): 9,
    ('Chinatown', 'Presidio'): 19,
    ('Chinatown', 'Haight-Ashbury'): 19,
    ('Chinatown', 'Nob Hill'): 9,
    ('Chinatown', 'Russian Hill'): 7,
    ('Chinatown', 'North Beach'): 3,
    ('Chinatown', 'Union Square'): 7,
    ('Chinatown', 'Embarcadero'): 5,
    ('Chinatown', 'Financial District'): 5,
    ('Chinatown', 'Marina District'): 12,
    ('Union Square', 'Presidio'): 24,
    ('Union Square', 'Haight-Ashbury'): 18,
    ('Union Square', 'Nob Hill'): 9,
    ('Union Square', 'Russian Hill'): 13,
    ('Union Square', 'North Beach'): 10,
    ('Union Square', 'Chinatown'): 7,
    ('Union Square', 'Embarcadero'): 11,
    ('Union Square', 'Financial District'): 9,
    ('Union Square', 'Marina District'): 18,
    ('Embarcadero', 'Presidio'): 20,
    ('Embarcadero', 'Haight-Ashbury'): 21,
    ('Embarcadero', 'Nob Hill'): 10,
    ('Embarcadero', 'Russian Hill'): 8,
    ('Embarcadero', 'North Beach'): 5,
    ('Embarcadero', 'Chinatown'): 7,
    ('Embarcadero', 'Union Square'): 10,
    ('Embarcadero', 'Financial District'): 5,
    ('Embarcadero', 'Marina District'): 12,
    ('Financial District', 'Presidio'): 22,
    ('Financial District', 'Haight-Ashbury'): 19,
    ('Financial District', 'Nob Hill'): 8,
    ('Financial District', 'Russian Hill'): 11,
    ('Financial District', 'North Beach'): 7,
    ('Financial District', 'Chinatown'): 5,
    ('Financial District', 'Union Square'): 9,
    ('Financial District', 'Embarcadero'): 4,
    ('Financial District', 'Marina District'): 15,
    ('Marina District', 'Presidio'): 10,
    ('Marina District', 'Haight-Ashbury'): 16,
    ('Marina District', 'Nob Hill'): 12,
    ('Marina District', 'Russian Hill'): 8,
    ('Marina District', 'North Beach'): 11,
    ('Marina District', 'Chinatown'): 15,
    ('Marina District', 'Union Square'): 16,
    ('Marina District', 'Embarcadero'): 14,
    ('Marina District', 'Financial District'): 17,
}

# Define constraints
constraints = {
    'Karen': {'location': 'Haight-Ashbury', 'start': '21:00', 'end': '21:45', 'min_duration': 45},
    'Jessica': {'location': 'Nob Hill', 'start': '13:45', 'end': '21:00', 'min_duration': 90},
    'Brian': {'location': 'Russian Hill', 'start': '15:30', 'end': '21:45', 'min_duration': 60},
    'Kenneth': {'location': 'North Beach', 'start': '9:45', 'end': '21:00', 'min_duration': 30},
    'Jason': {'location': 'Chinatown', 'start': '8:15', 'end': '11:45', 'min_duration': 75},
    'Stephanie': {'location': 'Union Square', 'start': '14:45', 'end': '18:45', 'min_duration': 105},
    'Kimberly': {'location': 'Embarcadero', 'start': '9:45', 'end': '19:30', 'min_duration': 75},
    'Steven': {'location': 'Financial District', 'start': '7:15', 'end': '21:15', 'min_duration': 60},
    'Mark': {'location': 'Marina District', 'start': '10:15', 'end': '13:00', 'min_duration': 75},
}

def parse_time(time_str):
    return datetime.strptime(time_str, '%H:%M')

def add_minutes(time, minutes):
    return time + timedelta(minutes=minutes)

def can_meet(start, end, min_duration):
    return (end - start).total_seconds() / 60 >= min_duration

def find_best_schedule(constraints, travel_times):
    start_time = parse_time('9:00')
    current_location = 'Presidio'
    itinerary = []

    def dfs(current_time, current_location, visited):
        nonlocal itinerary
        best_itinerary = []
        best_end_time = None

        for person, details in constraints.items():
            if person not in visited:
                location = details['location']
                start = parse_time(details['start'])
                end = parse_time(details['end'])
                min_duration = details['min_duration']

                travel_time = travel_times[(current_location, location)]
                arrival_time = add_minutes(current_time, travel_time)

                if arrival_time < start:
                    meeting_start = start
                else:
                    meeting_start = arrival_time

                meeting_end = add_minutes(meeting_start, min_duration)

                if meeting_end <= end:
                    new_visited = visited | {person}
                    remaining_itinerary, remaining_end_time = dfs(meeting_end, location, new_visited)

                    if remaining_end_time is not None:
                        current_itinerary = [{'action': 'meet', 'location': location, 'person': person,
                                              'start_time': meeting_start.strftime('%H:%M'),
                                              'end_time': meeting_end.strftime('%H:%M')}] + remaining_itinerary
                        if best_end_time is None or remaining_end_time > best_end_time:
                            best_itinerary = current_itinerary
                            best_end_time = remaining_end_time

        if best_end_time is None:
            return [], current_time

        return best_itinerary, best_end_time

    itinerary, _ = dfs(start_time, current_location, set())
    return itinerary

itinerary = find_best_schedule(constraints, travel_times)
print(json.dumps({"itinerary": itinerary}, indent=2))