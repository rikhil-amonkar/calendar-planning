import json
from datetime import datetime, timedelta

# Define travel times
travel_times = {
    ('Nob Hill', 'Richmond District'): 14,
    ('Nob Hill', 'Financial District'): 9,
    ('Nob Hill', 'North Beach'): 8,
    ('Nob Hill', 'The Castro'): 17,
    ('Nob Hill', 'Golden Gate Park'): 17,
    ('Richmond District', 'Nob Hill'): 17,
    ('Richmond District', 'Financial District'): 22,
    ('Richmond District', 'North Beach'): 17,
    ('Richmond District', 'The Castro'): 16,
    ('Richmond District', 'Golden Gate Park'): 9,
    ('Financial District', 'Nob Hill'): 8,
    ('Financial District', 'Richmond District'): 21,
    ('Financial District', 'North Beach'): 7,
    ('Financial District', 'The Castro'): 23,
    ('Financial District', 'Golden Gate Park'): 23,
    ('North Beach', 'Nob Hill'): 7,
    ('North Beach', 'Richmond District'): 18,
    ('North Beach', 'Financial District'): 8,
    ('North Beach', 'The Castro'): 22,
    ('North Beach', 'Golden Gate Park'): 22,
    ('The Castro', 'Nob Hill'): 16,
    ('The Castro', 'Richmond District'): 16,
    ('The Castro', 'Financial District'): 20,
    ('The Castro', 'North Beach'): 20,
    ('The Castro', 'Golden Gate Park'): 11,
    ('Golden Gate Park', 'Nob Hill'): 20,
    ('Golden Gate Park', 'Richmond District'): 7,
    ('Golden Gate Park', 'Financial District'): 26,
    ('Golden Gate Park', 'North Beach'): 24,
    ('Golden Gate Park', 'The Castro'): 13,
}

# Define meeting constraints
meetings = {
    'Emily': {'location': 'Richmond District', 'start': '19:00', 'end': '21:00', 'min_duration': 15},
    'Margaret': {'location': 'Financial District', 'start': '16:30', 'end': '20:15', 'min_duration': 75},
    'Ronald': {'location': 'North Beach', 'start': '18:30', 'end': '19:30', 'min_duration': 45},
    'Deborah': {'location': 'The Castro', 'start': '13:45', 'end': '21:15', 'min_duration': 90},
    'Jeffrey': {'location': 'Golden Gate Park', 'start': '11:15', 'end': '14:30', 'min_duration': 120},
}

def parse_time(time_str):
    return datetime.strptime(time_str, '%H:%M')

def format_time(time_obj):
    return time_obj.strftime('%H:%M').lstrip('0')

def find_optimal_schedule():
    start_time = parse_time('9:00')
    current_location = 'Nob Hill'
    itinerary = []

    def can_meet(person, current_time):
        meeting = meetings[person]
        meeting_start = parse_time(meeting['start'])
        meeting_end = parse_time(meeting['end'])
        min_duration = meeting['min_duration']
        available_time = (meeting_end - current_time).total_seconds() / 60
        return current_time <= meeting_start and available_time >= min_duration

    def get_travel_time(from_loc, to_loc):
        return travel_times.get((from_loc, to_loc), float('inf'))

    def add_meeting_to_itinerary(person, current_time):
        meeting = meetings[person]
        meeting_start = parse_time(meeting['start'])
        meeting_end = parse_time(meeting['end'])
        min_duration = meeting['min_duration']
        start_meeting_time = max(current_time, meeting_start)
        end_meeting_time = start_meeting_time + timedelta(minutes=min_duration)
        if end_meeting_time > meeting_end:
            end_meeting_time = meeting_end
        itinerary.append({
            "action": "meet",
            "location": meeting['location'],
            "person": person,
            "start_time": format_time(start_meeting_time),
            "end_time": format_time(end_meeting_time)
        })
        return end_meeting_time

    # Sort meetings by earliest possible start time
    sorted_meetings = sorted(meetings.keys(), key=lambda x: parse_time(meetings[x]['start']))

    for person in sorted_meetings:
        meeting = meetings[person]
        meeting_location = meeting['location']
        travel_time = get_travel_time(current_location, meeting_location)
        arrival_time = start_time + timedelta(minutes=travel_time)

        if can_meet(person, arrival_time):
            start_time = add_meeting_to_itinerary(person, arrival_time)
            current_location = meeting_location
        else:
            # If we can't meet at the current location, try to adjust the schedule
            # This is a simple heuristic: try to meet as late as possible before the meeting ends
            meeting_start = parse_time(meeting['start'])
            meeting_end = parse_time(meeting['end'])
            min_duration = meeting['min_duration']
            if meeting_start <= start_time + timedelta(minutes=travel_time) <= meeting_end:
                start_time = add_meeting_to_itinerary(person, meeting_start)
                current_location = meeting_location

    return itinerary

optimal_itinerary = find_optimal_schedule()
result = {"itinerary": optimal_itinerary}
print(json.dumps(result, indent=2))