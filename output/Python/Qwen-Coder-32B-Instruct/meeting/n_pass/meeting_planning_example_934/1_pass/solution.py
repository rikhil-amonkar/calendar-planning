import json
from datetime import datetime, timedelta

# Define travel times
travel_times = {
    ('Nob Hill', 'Embarcadero'): 9, ('Embarcadero', 'Nob Hill'): 10,
    ('Nob Hill', 'The Castro'): 17, ('The Castro', 'Nob Hill'): 16,
    ('Nob Hill', 'Haight-Ashbury'): 13, ('Haight-Ashbury', 'Nob Hill'): 15,
    ('Nob Hill', 'Union Square'): 7, ('Union Square', 'Nob Hill'): 9,
    ('Nob Hill', 'North Beach'): 8, ('North Beach', 'Nob Hill'): 7,
    ('Nob Hill', 'Pacific Heights'): 8, ('Pacific Heights', 'Nob Hill'): 8,
    ('Nob Hill', 'Chinatown'): 6, ('Chinatown', 'Nob Hill'): 9,
    ('Nob Hill', 'Golden Gate Park'): 17, ('Golden Gate Park', 'Nob Hill'): 20,
    ('Nob Hill', 'Marina District'): 11, ('Marina District', 'Nob Hill'): 12,
    ('Nob Hill', 'Russian Hill'): 5, ('Russian Hill', 'Nob Hill'): 5,
    ('Embarcadero', 'The Castro'): 25, ('The Castro', 'Embarcadero'): 22,
    ('Embarcadero', 'Haight-Ashbury'): 21, ('Haight-Ashbury', 'Embarcadero'): 20,
    ('Embarcadero', 'Union Square'): 10, ('Union Square', 'Embarcadero'): 11,
    ('Embarcadero', 'North Beach'): 5, ('North Beach', 'Embarcadero'): 6,
    ('Embarcadero', 'Pacific Heights'): 11, ('Pacific Heights', 'Embarcadero'): 10,
    ('Embarcadero', 'Chinatown'): 7, ('Chinatown', 'Embarcadero'): 5,
    ('Embarcadero', 'Golden Gate Park'): 25, ('Golden Gate Park', 'Embarcadero'): 25,
    ('Embarcadero', 'Marina District'): 12, ('Marina District', 'Embarcadero'): 14,
    ('Embarcadero', 'Russian Hill'): 8, ('Russian Hill', 'Embarcadero'): 8,
    ('The Castro', 'Haight-Ashbury'): 6, ('Haight-Ashbury', 'The Castro'): 6,
    ('The Castro', 'Union Square'): 19, ('Union Square', 'The Castro'): 17,
    ('The Castro', 'North Beach'): 20, ('North Beach', 'The Castro'): 23,
    ('The Castro', 'Pacific Heights'): 16, ('Pacific Heights', 'The Castro'): 16,
    ('The Castro', 'Chinatown'): 22, ('Chinatown', 'The Castro'): 22,
    ('The Castro', 'Golden Gate Park'): 11, ('Golden Gate Park', 'The Castro'): 13,
    ('The Castro', 'Marina District'): 21, ('Marina District', 'The Castro'): 22,
    ('The Castro', 'Russian Hill'): 18, ('Russian Hill', 'The Castro'): 21,
    ('Haight-Ashbury', 'Union Square'): 19, ('Union Square', 'Haight-Ashbury'): 18,
    ('Haight-Ashbury', 'North Beach'): 19, ('North Beach', 'Haight-Ashbury'): 18,
    ('Haight-Ashbury', 'Pacific Heights'): 12, ('Pacific Heights', 'Haight-Ashbury'): 11,
    ('Haight-Ashbury', 'Chinatown'): 19, ('Chinatown', 'Haight-Ashbury'): 19,
    ('Haight-Ashbury', 'Golden Gate Park'): 7, ('Golden Gate Park', 'Haight-Ashbury'): 7,
    ('Haight-Ashbury', 'Marina District'): 17, ('Marina District', 'Haight-Ashbury'): 16,
    ('Haight-Ashbury', 'Russian Hill'): 17, ('Russian Hill', 'Haight-Ashbury'): 17,
    ('Union Square', 'North Beach'): 10, ('North Beach', 'Union Square'): 7,
    ('Union Square', 'Pacific Heights'): 15, ('Pacific Heights', 'Union Square'): 12,
    ('Union Square', 'Chinatown'): 7, ('Chinatown', 'Union Square'): 7,
    ('Union Square', 'Golden Gate Park'): 22, ('Golden Gate Park', 'Union Square'): 22,
    ('Union Square', 'Marina District'): 18, ('Marina District', 'Union Square'): 16,
    ('Union Square', 'Russian Hill'): 13, ('Russian Hill', 'Union Square'): 10,
    ('North Beach', 'Pacific Heights'): 8, ('Pacific Heights', 'North Beach'): 9,
    ('North Beach', 'Chinatown'): 6, ('Chinatown', 'North Beach'): 3,
    ('North Beach', 'Golden Gate Park'): 22, ('Golden Gate Park', 'North Beach'): 23,
    ('North Beach', 'Marina District'): 9, ('Marina District', 'North Beach'): 11,
    ('North Beach', 'Russian Hill'): 4, ('Russian Hill', 'North Beach'): 5,
    ('Pacific Heights', 'Chinatown'): 11, ('Chinatown', 'Pacific Heights'): 10,
    ('Pacific Heights', 'Golden Gate Park'): 15, ('Golden Gate Park', 'Pacific Heights'): 16,
    ('Pacific Heights', 'Marina District'): 6, ('Marina District', 'Pacific Heights'): 7,
    ('Pacific Heights', 'Russian Hill'): 7, ('Russian Hill', 'Pacific Heights'): 7,
    ('Chinatown', 'Golden Gate Park'): 23, ('Golden Gate Park', 'Chinatown'): 23,
    ('Chinatown', 'Marina District'): 12, ('Marina District', 'Chinatown'): 15,
    ('Chinatown', 'Russian Hill'): 9, ('Russian Hill', 'Chinatown'): 9,
    ('Golden Gate Park', 'Marina District'): 16, ('Marina District', 'Golden Gate Park'): 18,
    ('Golden Gate Park', 'Russian Hill'): 19, ('Russian Hill', 'Golden Gate Park'): 21,
    ('Marina District', 'Russian Hill'): 8, ('Russian Hill', 'Marina District'): 7,
}

# Define meetings
meetings = {
    'Mary': {'location': 'Embarcadero', 'start': '20:00', 'end': '21:15', 'min_duration': 75},
    'Kenneth': {'location': 'The Castro', 'start': '11:15', 'end': '19:15', 'min_duration': 30},
    'Joseph': {'location': 'Haight-Ashbury', 'start': '20:00', 'end': '22:00', 'min_duration': 120},
    'Sarah': {'location': 'Union Square', 'start': '11:45', 'end': '14:30', 'min_duration': 90},
    'Thomas': {'location': 'North Beach', 'start': '19:15', 'end': '19:45', 'min_duration': 15},
    'Daniel': {'location': 'Pacific Heights', 'start': '13:45', 'end': '20:30', 'min_duration': 15},
    'Richard': {'location': 'Chinatown', 'start': '08:00', 'end': '18:45', 'min_duration': 30},
    'Mark': {'location': 'Golden Gate Park', 'start': '17:30', 'end': '21:30', 'min_duration': 120},
    'David': {'location': 'Marina District', 'start': '20:00', 'end': '21:00', 'min_duration': 60},
    'Karen': {'location': 'Russian Hill', 'start': '13:15', 'end': '18:30', 'min_duration': 120},
}

def parse_time(time_str):
    return datetime.strptime(time_str, '%H:%M')

def time_to_str(dt):
    return dt.strftime('%H:%M')

def can_meet(start, end, min_duration):
    return (end - start).total_seconds() / 60 >= min_duration

def find_schedule():
    current_time = parse_time('09:00')
    current_location = 'Nob Hill'
    itinerary = []

    def add_meeting(person, location, start, end):
        nonlocal current_time, current_location
        travel_time = travel_times.get((current_location, location), float('inf'))
        if (start - current_time).total_seconds() / 60 < travel_time + min_duration:
            return False
        current_time += timedelta(minutes=travel_time)
        itinerary.append({
            'action': 'meet',
            'location': location,
            'person': person,
            'start_time': time_to_str(current_time),
            'end_time': time_to_str(min(end, current_time + timedelta(minutes=min_duration)))
        })
        current_time += timedelta(minutes=min_duration)
        current_location = location
        return True

    # Prioritize meetings with longer durations first
    sorted_meetings = sorted(meetings.items(), key=lambda x: -x[1]['min_duration'])

    for person, details in sorted_meetings:
        start = parse_time(details['start'])
        end = parse_time(details['end'])
        min_duration = details['min_duration']
        if can_meet(start, end, min_duration):
            add_meeting(person, details['location'], start, end)

    return itinerary

itinerary = find_schedule()
result = {'itinerary': itinerary}
print(json.dumps(result))