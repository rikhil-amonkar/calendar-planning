import json
from datetime import datetime, timedelta

# Define the travel times
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

# Define the meeting constraints
meetings = {
    'Mary': {'location': 'Golden Gate Park', 'start': '8:45', 'end': '11:45', 'min_duration': 45},
    'Kevin': {'location': 'Haight-Ashbury', 'start': '10:15', 'end': '16:15', 'min_duration': 90},
    'Deborah': {'location': 'Bayview', 'start': '15:00', 'end': '19:15', 'min_duration': 120},
    'Stephanie': {'location': 'Presidio', 'start': '10:00', 'end': '17:15', 'min_duration': 120},
    'Emily': {'location': 'Financial District', 'start': '11:30', 'end': '21:45', 'min_duration': 105},
}

def parse_time(time_str):
    return datetime.strptime(time_str, '%H:%M').time()

def format_time(dt):
    return dt.strftime('%H:%M')

def find_optimal_schedule(start_time, meetings, travel_times):
    def can_meet(meeting, current_time):
        meeting_start = parse_time(meeting['start'])
        meeting_end = parse_time(meeting['end'])
        min_duration = timedelta(minutes=meeting['min_duration'])
        return current_time <= meeting_start and meeting_end - timedelta(hours=meeting_start.hour, minutes=meeting_start.minute) >= min_duration

    def find_next_meeting(current_location, current_time):
        next_meeting = None
        for person, meeting in meetings.items():
            if can_meet(meeting, current_time):
                location = meeting['location']
                travel_time = travel_times[(current_location, location)]
                arrival_time = datetime.combine(datetime.today(), current_time) + timedelta(minutes=travel_time)
                meeting_start = datetime.combine(datetime.today(), parse_time(meeting['start']))
                meeting_end = datetime.combine(datetime.today(), parse_time(meeting['end']))
                min_duration = timedelta(minutes=meeting['min_duration'])

                # Ensure the meeting starts within the available window
                if arrival_time.time() < meeting_start.time():
                    potential_start = meeting_start
                else:
                    potential_start = arrival_time

                if potential_start + min_duration <= meeting_end:
                    if next_meeting is None or potential_start < next_meeting[0]:
                        next_meeting = (potential_start.time(), location, person)
        return next_meeting

    itinerary = []
    current_location = 'Embarcadero'
    current_time = start_time
    available_meetings = dict(meetings)

    while available_meetings:
        next_meeting = find_next_meeting(current_location, current_time)
        if next_meeting is None:
            break
        meeting_start, location, person = next_meeting
        meeting = available_meetings.pop(person)
        meeting_end = datetime.combine(datetime.today(), parse_time(meeting['end']))
        min_duration = timedelta(minutes=meeting['min_duration'])
        meeting_end = max(datetime.combine(datetime.today(), meeting_start), meeting_end - min_duration)
        itinerary.append({
            "action": "meet",
            "location": location,
            "person": person,
            "start_time": format_time(meeting_start),
            "end_time": format_time(meeting_end.time())
        })
        current_location = location
        current_time = meeting_end.time()

    return itinerary

optimal_itinerary = find_optimal_schedule(parse_time('9:00'), meetings, travel_times)
output = {"itinerary": optimal_itinerary}
print(json.dumps(output, indent=2))