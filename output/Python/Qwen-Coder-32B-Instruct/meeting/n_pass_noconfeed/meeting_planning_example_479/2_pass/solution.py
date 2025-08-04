import json
from datetime import datetime, timedelta

# Define travel times
travel_times = {
    ('Embarcadero', 'Golden Gate Park'): 25,
    ('Embarcadero', 'Haight-Ashbury'): 21,
    ('Embarcadero', 'Bayview'): 21,
    ('Embarcadero', 'Presidio'): 20,
    ('Embarcadero', 'Financial District'): 5,
    ('Golden Gate Park', 'Embarcadero'): 25,
    ('Golden Gate Park', 'Haight-Ashbury'): 7,
    ('Golden Gate Park', 'Bayview'): 23,
    ('Golden Gate Park', 'Presidio'): 11,
    ('Golden Gate Park', 'Financial District'): 26,
    ('Haight-Ashbury', 'Embarcadero'): 20,
    ('Haight-Ashbury', 'Golden Gate Park'): 7,
    ('Haight-Ashbury', 'Bayview'): 18,
    ('Haight-Ashbury', 'Presidio'): 15,
    ('Haight-Ashbury', 'Financial District'): 21,
    ('Bayview', 'Embarcadero'): 19,
    ('Bayview', 'Golden Gate Park'): 22,
    ('Bayview', 'Haight-Ashbury'): 19,
    ('Bayview', 'Presidio'): 31,
    ('Bayview', 'Financial District'): 19,
    ('Presidio', 'Embarcadero'): 20,
    ('Presidio', 'Golden Gate Park'): 12,
    ('Presidio', 'Haight-Ashbury'): 15,
    ('Presidio', 'Bayview'): 31,
    ('Presidio', 'Financial District'): 23,
    ('Financial District', 'Embarcadero'): 4,
    ('Financial District', 'Golden Gate Park'): 23,
    ('Financial District', 'Haight-Ashbury'): 19,
    ('Financial District', 'Bayview'): 19,
    ('Financial District', 'Presidio'): 22,
}

# Define meeting constraints
meetings = {
    'Mary': {'location': 'Golden Gate Park', 'start': '8:45', 'end': '11:45', 'min_duration': 45},
    'Kevin': {'location': 'Haight-Ashbury', 'start': '10:15', 'end': '16:15', 'min_duration': 90},
    'Deborah': {'location': 'Bayview', 'start': '15:00', 'end': '19:15', 'min_duration': 120},
    'Stephanie': {'location': 'Presidio', 'start': '10:00', 'end': '17:15', 'min_duration': 120},
    'Emily': {'location': 'Financial District', 'start': '11:30', 'end': '21:45', 'min_duration': 105},
}

def parse_time(time_str):
    return datetime.strptime(time_str, '%H:%M')

def add_minutes(time_obj, minutes):
    return time_obj + timedelta(minutes=minutes)

def format_time(time_obj):
    return time_obj.strftime('%H:%M')

def find_schedule(start_location, start_time, meetings, travel_times):
    def is_valid_meeting(meeting, current_time):
        meeting_start = parse_time(meeting['start'])
        meeting_end = parse_time(meeting['end'])
        min_duration = meeting['min_duration']
        return meeting_start <= current_time <= add_minutes(meeting_end, -min_duration)

    def get_next_location(current_location, current_time):
        best_location = None
        best_time = None
        for person, meeting in meetings.items():
            if is_valid_meeting(meeting, current_time):
                location = meeting['location']
                if location != current_location:  # Ensure we don't try to travel to the same location
                    travel_time = travel_times[(current_location, location)]
                    arrival_time = add_minutes(current_time, travel_time)
                    if is_valid_meeting(meeting, arrival_time):
                        end_time = add_minutes(arrival_time, meeting['min_duration'])
                        if best_time is None or end_time < best_time:
                            best_time = end_time
                            best_location = (location, arrival_time, end_time, person)
        return best_location

    itinerary = []
    current_location = start_location
    current_time = parse_time(start_time)

    while True:
        next_location = get_next_location(current_location, current_time)
        if next_location is None:
            break
        location, arrival_time, end_time, person = next_location
        itinerary.append({
            "action": "meet",
            "location": location,
            "person": person,
            "start_time": format_time(arrival_time),
            "end_time": format_time(end_time)
        })
        current_location = location
        current_time = end_time

    return itinerary

start_location = 'Embarcadero'
start_time = '9:00'

itinerary = find_schedule(start_location, start_time, meetings, travel_times)
result = {"itinerary": itinerary}
print(json.dumps(result))