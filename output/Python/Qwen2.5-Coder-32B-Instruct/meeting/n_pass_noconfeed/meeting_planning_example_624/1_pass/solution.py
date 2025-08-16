import json
from datetime import datetime, timedelta

# Define travel times
travel_times = {
    ('Golden Gate Park', 'Haight-Ashbury'): 7,
    ('Golden Gate Park', 'Fisherman\'s Wharf'): 24,
    ('Golden Gate Park', 'The Castro'): 13,
    ('Golden Gate Park', 'Chinatown'): 23,
    ('Golden Gate Park', 'Alamo Square'): 10,
    ('Golden Gate Park', 'North Beach'): 24,
    ('Golden Gate Park', 'Russian Hill'): 19,
    ('Haight-Ashbury', 'Golden Gate Park'): 7,
    ('Haight-Ashbury', 'Fisherman\'s Wharf'): 23,
    ('Haight-Ashbury', 'The Castro'): 6,
    ('Haight-Ashbury', 'Chinatown'): 19,
    ('Haight-Ashbury', 'Alamo Square'): 5,
    ('Haight-Ashbury', 'North Beach'): 19,
    ('Haight-Ashbury', 'Russian Hill'): 17,
    ('Fisherman\'s Wharf', 'Golden Gate Park'): 25,
    ('Fisherman\'s Wharf', 'Haight-Ashbury'): 22,
    ('Fisherman\'s Wharf', 'The Castro'): 26,
    ('Fisherman\'s Wharf', 'Chinatown'): 12,
    ('Fisherman\'s Wharf', 'Alamo Square'): 20,
    ('Fisherman\'s Wharf', 'North Beach'): 6,
    ('Fisherman\'s Wharf', 'Russian Hill'): 7,
    ('The Castro', 'Golden Gate Park'): 11,
    ('The Castro', 'Haight-Ashbury'): 6,
    ('The Castro', 'Fisherman\'s Wharf'): 24,
    ('The Castro', 'Chinatown'): 20,
    ('The Castro', 'Alamo Square'): 8,
    ('The Castro', 'North Beach'): 20,
    ('The Castro', 'Russian Hill'): 18,
    ('Chinatown', 'Golden Gate Park'): 23,
    ('Chinatown', 'Haight-Ashbury'): 19,
    ('Chinatown', 'Fisherman\'s Wharf'): 8,
    ('Chinatown', 'The Castro'): 22,
    ('Chinatown', 'Alamo Square'): 17,
    ('Chinatown', 'North Beach'): 3,
    ('Chinatown', 'Russian Hill'): 7,
    ('Alamo Square', 'Golden Gate Park'): 9,
    ('Alamo Square', 'Haight-Ashbury'): 5,
    ('Alamo Square', 'Fisherman\'s Wharf'): 19,
    ('Alamo Square', 'The Castro'): 8,
    ('Alamo Square', 'Chinatown'): 16,
    ('Alamo Square', 'North Beach'): 15,
    ('Alamo Square', 'Russian Hill'): 13,
    ('North Beach', 'Golden Gate Park'): 22,
    ('North Beach', 'Haight-Ashbury'): 18,
    ('North Beach', 'Fisherman\'s Wharf'): 5,
    ('North Beach', 'The Castro'): 22,
    ('North Beach', 'Chinatown'): 6,
    ('North Beach', 'Alamo Square'): 16,
    ('North Beach', 'Russian Hill'): 4,
    ('Russian Hill', 'Golden Gate Park'): 21,
    ('Russian Hill', 'Haight-Ashbury'): 17,
    ('Russian Hill', 'Fisherman\'s Wharf'): 7,
    ('Russian Hill', 'The Castro'): 21,
    ('Russian Hill', 'Chinatown'): 9,
    ('Russian Hill', 'Alamo Square'): 15,
    ('Russian Hill', 'North Beach'): 5,
}

# Define meeting constraints
meetings = {
    'Carol': {'location': 'Haight-Ashbury', 'start': '21:30', 'end': '22:30', 'min_duration': 60},
    'Laura': {'location': 'Fisherman\'s Wharf', 'start': '11:45', 'end': '21:30', 'min_duration': 60},
    'Karen': {'location': 'The Castro', 'start': '7:15', 'end': '14:00', 'min_duration': 75},
    'Elizabeth': {'location': 'Chinatown', 'start': '12:15', 'end': '21:30', 'min_duration': 75},
    'Deborah': {'location': 'Alamo Square', 'start': '12:00', 'end': '15:00', 'min_duration': 105},
    'Jason': {'location': 'North Beach', 'start': '14:45', 'end': '19:00', 'min_duration': 90},
    'Steven': {'location': 'Russian Hill', 'start': '14:45', 'end': '18:30', 'min_duration': 120},
}

def parse_time(time_str):
    return datetime.strptime(time_str, '%H:%M')

def can_meet(start, end, min_duration):
    return (parse_time(end) - parse_time(start)).total_seconds() / 60 >= min_duration

def find_best_schedule():
    start_time = parse_time('9:00')
    current_location = 'Golden Gate Park'
    itinerary = []

    def add_meeting(person, location, start, end):
        nonlocal start_time, current_location
        travel_time = travel_times.get((current_location, location), float('inf'))
        arrival_time = start_time + timedelta(minutes=travel_time)
        if arrival_time < parse_time(start):
            meeting_start = parse_time(start)
        else:
            meeting_start = arrival_time
        meeting_end = parse_time(end)
        if can_meet(meeting_start.strftime('%H:%M'), meeting_end.strftime('%H:%M'), meetings[person]['min_duration']):
            itinerary.append({
                "action": "meet",
                "location": location,
                "person": person,
                "start_time": meeting_start.strftime('%H:%M'),
                "end_time": meeting_end.strftime('%H:%M')
            })
            start_time = meeting_end
            current_location = location

    # Sort meetings by start time
    sorted_meetings = sorted(meetings.items(), key=lambda x: parse_time(x[1]['start']))

    for person, details in sorted_meetings:
        add_meeting(person, details['location'], details['start'], details['end'])

    return itinerary

itinerary = find_best_schedule()
result = {"itinerary": itinerary}
print(json.dumps(result))