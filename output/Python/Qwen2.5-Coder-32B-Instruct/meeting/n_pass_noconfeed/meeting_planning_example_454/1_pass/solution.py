import json
from datetime import datetime, timedelta

# Define travel times
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

# Define meeting constraints
meetings = {
    'Jessica': {'location': 'Golden Gate Park', 'start': '13:45', 'end': '15:00', 'min_duration': 30},
    'Ashley': {'location': 'Bayview', 'start': '17:15', 'end': '20:00', 'min_duration': 105},
    'Ronald': {'location': 'Chinatown', 'start': '07:15', 'end': '14:45', 'min_duration': 90},
    'William': {'location': 'North Beach', 'start': '13:15', 'end': '20:15', 'min_duration': 15},
    'Daniel': {'location': 'Mission District', 'start': '07:00', 'end': '11:15', 'min_duration': 105},
}

def parse_time(time_str):
    return datetime.strptime(time_str, '%H:%M')

def time_to_str(time_obj):
    return time_obj.strftime('%H:%M')

def find_meeting_schedule():
    start_time = parse_time('09:00')
    current_location = 'Presidio'
    itinerary = []

    def can_meet(meeting, current_time, current_location):
        meeting_start = parse_time(meeting['start'])
        meeting_end = parse_time(meeting['end'])
        min_duration = timedelta(minutes=meeting['min_duration'])
        travel_time = timedelta(minutes=travel_times[(current_location, meeting['location'])])
        return current_time + travel_time <= meeting_start and meeting_end - meeting_start >= min_duration

    def add_meeting_to_itinerary(meeting, current_time, current_location):
        travel_time = timedelta(minutes=travel_times[(current_location, meeting['location'])])
        start_time = current_time + travel_time
        end_time = start_time + timedelta(minutes=meeting['min_duration'])
        itinerary.append({
            'action': 'meet',
            'location': meeting['location'],
            'person': list(meetings.keys())[list(meetings.values()).index(meeting)],
            'start_time': time_to_str(start_time),
            'end_time': time_to_str(end_time)
        })
        return end_time, meeting['location']

    # Sort meetings by earliest possible start time
    sorted_meetings = sorted(meetings.values(), key=lambda x: parse_time(x['start']))

    for meeting in sorted_meetings:
        if can_meet(meeting, start_time, current_location):
            start_time, current_location = add_meeting_to_itinerary(meeting, start_time, current_location)

    return itinerary

itinerary = find_meeting_schedule()
result = {'itinerary': itinerary}
print(json.dumps(result))