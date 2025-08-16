import json
from datetime import datetime, timedelta

# Define travel times
travel_times = {
    ('Golden Gate Park', 'Haight-Ashbury'): 7,
    ('Golden Gate Park', 'Sunset District'): 10,
    ('Golden Gate Park', 'Marina District'): 16,
    ('Golden Gate Park', 'Financial District'): 26,
    ('Golden Gate Park', 'Union Square'): 22,
    ('Haight-Ashbury', 'Golden Gate Park'): 7,
    ('Haight-Ashbury', 'Sunset District'): 15,
    ('Haight-Ashbury', 'Marina District'): 17,
    ('Haight-Ashbury', 'Financial District'): 21,
    ('Haight-Ashbury', 'Union Square'): 17,
    ('Sunset District', 'Golden Gate Park'): 11,
    ('Sunset District', 'Haight-Ashbury'): 15,
    ('Sunset District', 'Marina District'): 21,
    ('Sunset District', 'Financial District'): 30,
    ('Sunset District', 'Union Square'): 30,
    ('Marina District', 'Golden Gate Park'): 18,
    ('Marina District', 'Haight-Ashbury'): 16,
    ('Marina District', 'Sunset District'): 19,
    ('Marina District', 'Financial District'): 17,
    ('Marina District', 'Union Square'): 16,
    ('Financial District', 'Golden Gate Park'): 23,
    ('Financial District', 'Haight-Ashbury'): 19,
    ('Financial District', 'Sunset District'): 31,
    ('Financial District', 'Marina District'): 15,
    ('Financial District', 'Union Square'): 9,
    ('Union Square', 'Golden Gate Park'): 22,
    ('Union Square', 'Haight-Ashbury'): 18,
    ('Union Square', 'Sunset District'): 26,
    ('Union Square', 'Marina District'): 18,
    ('Union Square', 'Financial District'): 9,
}

# Define meeting constraints
meetings = {
    'Sarah': {'location': 'Haight-Ashbury', 'start': '17:00', 'end': '21:30', 'min_duration': 105},
    'Patricia': {'location': 'Sunset District', 'start': '17:00', 'end': '19:45', 'min_duration': 45},
    'Matthew': {'location': 'Marina District', 'start': '09:15', 'end': '12:00', 'min_duration': 15},
    'Joseph': {'location': 'Financial District', 'start': '14:15', 'end': '18:45', 'min_duration': 30},
    'Robert': {'location': 'Union Square', 'start': '10:15', 'end': '21:45', 'min_duration': 15},
}

def parse_time(time_str):
    return datetime.strptime(time_str, '%H:%M').time()

def time_to_str(time_obj):
    return time_obj.strftime('%H:%M')

def can_meet(start, end, min_duration):
    return (datetime.combine(datetime.min, end) - datetime.combine(datetime.min, start)).total_seconds() / 60 >= min_duration

def find_optimal_schedule():
    start_time = datetime.strptime('09:00', '%H:%M').time()
    current_location = 'Golden Gate Park'
    itinerary = []

    def try_meeting(person, location, start, end, min_duration):
        nonlocal start_time, current_location
        travel_time = travel_times[(current_location, location)]
        arrival_time = datetime.combine(datetime.min, start_time) + timedelta(minutes=travel_time)
        if arrival_time.time() >= end:
            return False  # Cannot reach the meeting on time
        meeting_start = max(arrival_time.time(), start)
        meeting_end = min(datetime.combine(datetime.min, meeting_start) + timedelta(minutes=min_duration), datetime.combine(datetime.min, end)).time()
        if can_meet(meeting_start, meeting_end, min_duration):
            itinerary.append({
                "action": "meet",
                "location": location,
                "person": person,
                "start_time": time_to_str(meeting_start),
                "end_time": time_to_str(meeting_end)
            })
            start_time = meeting_end
            current_location = location
            return True
        return False

    # Sort meetings by start time and then by the latest possible end time
    sorted_meetings = sorted(meetings.items(), key=lambda x: (parse_time(x[1]['start']), -datetime.combine(datetime.min, parse_time(x[1]['end'])).timestamp()))

    for person, details in sorted_meetings:
        try_meeting(person, details['location'], parse_time(details['start']), parse_time(details['end']), details['min_duration'])

    return itinerary

optimal_itinerary = find_optimal_schedule()
print(json.dumps({"itinerary": optimal_itinerary}))