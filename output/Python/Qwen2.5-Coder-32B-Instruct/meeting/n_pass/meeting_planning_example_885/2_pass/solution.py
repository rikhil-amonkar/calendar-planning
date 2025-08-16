import json
from datetime import datetime, timedelta

# Define travel times
travel_times = {
    ('Russian Hill', 'Marina District'): 7,
    ('Russian Hill', 'Financial District'): 11,
    ('Russian Hill', 'Alamo Square'): 15,
    ('Russian Hill', 'Golden Gate Park'): 21,
    ('Russian Hill', 'The Castro'): 21,
    ('Russian Hill', 'Bayview'): 23,
    ('Russian Hill', 'Sunset District'): 23,
    ('Russian Hill', 'Haight-Ashbury'): 17,
    ('Russian Hill', 'Nob Hill'): 5,
    ('Marina District', 'Russian Hill'): 8,
    ('Marina District', 'Financial District'): 17,
    ('Marina District', 'Alamo Square'): 15,
    ('Marina District', 'Golden Gate Park'): 18,
    ('Marina District', 'The Castro'): 22,
    ('Marina District', 'Bayview'): 27,
    ('Marina District', 'Sunset District'): 19,
    ('Marina District', 'Haight-Ashbury'): 16,
    ('Marina District', 'Nob Hill'): 12,
    ('Financial District', 'Russian Hill'): 11,
    ('Financial District', 'Marina District'): 15,
    ('Financial District', 'Alamo Square'): 17,
    ('Financial District', 'Golden Gate Park'): 23,
    ('Financial District', 'The Castro'): 20,
    ('Financial District', 'Bayview'): 19,
    ('Financial District', 'Sunset District'): 30,
    ('Financial District', 'Haight-Ashbury'): 19,
    ('Financial District', 'Nob Hill'): 8,
    ('Alamo Square', 'Russian Hill'): 13,
    ('Alamo Square', 'Marina District'): 15,
    ('Alamo Square', 'Financial District'): 17,
    ('Alamo Square', 'Golden Gate Park'): 9,
    ('Alamo Square', 'The Castro'): 8,
    ('Alamo Square', 'Bayview'): 16,
    ('Alamo Square', 'Sunset District'): 16,
    ('Alamo Square', 'Haight-Ashbury'): 5,
    ('Alamo Square', 'Nob Hill'): 11,
    ('Golden Gate Park', 'Russian Hill'): 19,
    ('Golden Gate Park', 'Marina District'): 16,
    ('Golden Gate Park', 'Financial District'): 26,
    ('Golden Gate Park', 'Alamo Square'): 9,
    ('Golden Gate Park', 'The Castro'): 13,
    ('Golden Gate Park', 'Bayview'): 23,
    ('Golden Gate Park', 'Sunset District'): 10,
    ('Golden Gate Park', 'Haight-Ashbury'): 7,
    ('Golden Gate Park', 'Nob Hill'): 20,
    ('The Castro', 'Russian Hill'): 18,
    ('The Castro', 'Marina District'): 21,
    ('The Castro', 'Financial District'): 21,
    ('The Castro', 'Alamo Square'): 8,
    ('The Castro', 'Golden Gate Park'): 11,
    ('The Castro', 'Bayview'): 19,
    ('The Castro', 'Sunset District'): 17,
    ('The Castro', 'Haight-Ashbury'): 6,
    ('The Castro', 'Nob Hill'): 16,
    ('Bayview', 'Russian Hill'): 23,
    ('Bayview', 'Marina District'): 27,
    ('Bayview', 'Financial District'): 19,
    ('Bayview', 'Alamo Square'): 16,
    ('Bayview', 'Golden Gate Park'): 22,
    ('Bayview', 'The Castro'): 19,
    ('Bayview', 'Sunset District'): 23,
    ('Bayview', 'Haight-Ashbury'): 19,
    ('Bayview', 'Nob Hill'): 20,
    ('Sunset District', 'Russian Hill'): 24,
    ('Sunset District', 'Marina District'): 21,
    ('Sunset District', 'Financial District'): 30,
    ('Sunset District', 'Alamo Square'): 17,
    ('Sunset District', 'Golden Gate Park'): 11,
    ('Sunset District', 'The Castro'): 17,
    ('Sunset District', 'Bayview'): 22,
    ('Sunset District', 'Haight-Ashbury'): 15,
    ('Sunset District', 'Nob Hill'): 27,
    ('Haight-Ashbury', 'Russian Hill'): 17,
    ('Haight-Ashbury', 'Marina District'): 17,
    ('Haight-Ashbury', 'Financial District'): 21,
    ('Haight-Ashbury', 'Alamo Square'): 5,
    ('Haight-Ashbury', 'Golden Gate Park'): 7,
    ('Haight-Ashbury', 'The Castro'): 6,
    ('Haight-Ashbury', 'Bayview'): 18,
    ('Haight-Ashbury', 'Sunset District'): 15,
    ('Haight-Ashbury', 'Nob Hill'): 15,
    ('Nob Hill', 'Russian Hill'): 5,
    ('Nob Hill', 'Marina District'): 11,
    ('Nob Hill', 'Financial District'): 9,
    ('Nob Hill', 'Alamo Square'): 11,
    ('Nob Hill', 'Golden Gate Park'): 17,
    ('Nob Hill', 'The Castro'): 17,
    ('Nob Hill', 'Bayview'): 19,
    ('Nob Hill', 'Sunset District'): 24,
    ('Nob Hill', 'Haight-Ashbury'): 13,
}

# Define constraints
constraints = {
    'Mark': {'location': 'Marina District', 'start': '18:45', 'end': '21:00', 'min_duration': 90},
    'Karen': {'location': 'Financial District', 'start': '9:30', 'end': '12:45', 'min_duration': 90},
    'Barbara': {'location': 'Alamo Square', 'start': '10:00', 'end': '19:30', 'min_duration': 90},
    'Nancy': {'location': 'Golden Gate Park', 'start': '16:45', 'end': '20:00', 'min_duration': 105},
    'David': {'location': 'The Castro', 'start': '9:00', 'end': '18:00', 'min_duration': 120},
    'Linda': {'location': 'Bayview', 'start': '18:15', 'end': '19:45', 'min_duration': 45},
    'Kevin': {'location': 'Sunset District', 'start': '10:00', 'end': '17:45', 'min_duration': 120},
    'Matthew': {'location': 'Haight-Ashbury', 'start': '10:15', 'end': '15:30', 'min_duration': 45},
    'Andrew': {'location': 'Nob Hill', 'start': '11:45', 'end': '16:45', 'min_duration': 105},
}

def parse_time(time_str):
    return datetime.strptime(time_str, '%H:%M')

def time_to_str(dt):
    return dt.strftime('%H:%M')

def can_meet(start, end, min_duration):
    return (end - start).total_seconds() / 60 >= min_duration

def find_meeting_schedule(constraints, travel_times):
    current_location = 'Russian Hill'
    current_time = parse_time('9:00')
    itinerary = []

    def get_next_location(current_time, current_location):
        best_location = None
        best_end_time = None
        for person, details in constraints.items():
            location = details['location']
            start = parse_time(details['start'])
            end = parse_time(details['end'])
            min_duration = details['min_duration']

            if current_time < start:
                travel_time = travel_times[(current_location, location)]
                arrival_time = current_time + timedelta(minutes=travel_time)
                if arrival_time < start:
                    continue
                meeting_start = start
            else:
                meeting_start = current_time

            if meeting_start >= end:
                continue

            meeting_end = min(meeting_start + timedelta(minutes=min_duration), end)

            if can_meet(meeting_start, meeting_end, min_duration):
                total_time = (meeting_end - current_time).total_seconds() / 60
                if best_end_time is None or total_time > (best_end_time - current_time).total_seconds() / 60:
                    best_location = location
                    best_end_time = meeting_end

        return best_location, best_end_time

    while True:
        next_location, next_end_time = get_next_location(current_time, current_location)
        if next_location is None:
            break

        travel_time = travel_times[(current_location, next_location)]
        arrival_time = current_time + timedelta(minutes=travel_time)

        itinerary.append({
            "action": "travel",
            "location": next_location,
            "start_time": time_to_str(current_time),
            "end_time": time_to_str(arrival_time)
        })

        meeting_start = max(arrival_time, parse_time(constraints[next_location]['start']))
        meeting_end = meeting_start + timedelta(minutes=constraints[next_location]['min_duration'])

        # Ensure meeting end does not exceed the person's availability
        if meeting_end > parse_time(constraints[next_location]['end']):
            meeting_end = parse_time(constraints[next_location]['end'])

        itinerary.append({
            "action": "meet",
            "location": next_location,
            "person": [k for k, v in constraints.items() if v['location'] == next_location][0],
            "start_time": time_to_str(meeting_start),
            "end_time": time_to_str(meeting_end)
        })

        current_time = meeting_end
        current_location = next_location

    return itinerary

itinerary = find_meeting_schedule(constraints, travel_times)
result = {"itinerary": itinerary}
print(json.dumps(result, indent=2))