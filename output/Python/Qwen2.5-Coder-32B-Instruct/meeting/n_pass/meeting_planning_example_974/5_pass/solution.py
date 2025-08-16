import json
from datetime import datetime, timedelta

# Define travel times in minutes
travel_times = {
    ('Sunset District', 'Downtown'): 30,
    ('Downtown', 'Sunset District'): 30,
    ('Sunset District', 'Golden Gate Park'): 20,
    ('Golden Gate Park', 'Sunset District'): 20,
    ('Downtown', 'Golden Gate Park'): 10,
    ('Golden Gate Park', 'Downtown'): 10
}

# Define meeting constraints
meetings = {
    'Alice': {'location': 'Downtown', 'start': '9:30', 'end': '10:30', 'min_duration': 30},
    'Bob': {'location': 'Golden Gate Park', 'start': '10:00', 'end': '11:00', 'min_duration': 30},
    'Charlie': {'location': 'Sunset District', 'start': '10:30', 'end': '11:30', 'min_duration': 30}
}

def time_to_minutes(time_str):
    parts = time_str.split(':')
    hours = int(parts[0].zfill(2))
    minutes = int(parts[1])
    return hours * 60 + minutes

def minutes_to_time(minutes):
    hours, minutes = divmod(minutes, 60)
    return f"{hours}:{minutes:02}"

def find_meeting_schedule(start_location, start_time, meetings, travel_times):
    def can_meet(meeting, current_time):
        meeting_start = time_to_minutes(meeting['start'])
        meeting_end = time_to_minutes(meeting['end'])
        return meeting_start <= current_time < meeting_end

    def get_available_meetings(current_time, current_location):
        available = []
        for person, details in meetings.items():
            if can_meet(details, current_time) and details['location'] != current_location:
                available.append((person, details))
        return available

    def find_best_meeting(current_time, current_location, visited):
        available_meetings = get_available_meetings(current_time, current_location)
        best_meeting = None
        best_score = -1
        for person, details in available_meetings:
            if person not in visited:
                travel_time = travel_times[(current_location, details['location'])]
                meeting_start = max(current_time + travel_time, time_to_minutes(details['start']))
                meeting_end = min(meeting_start + details['min_duration'], time_to_minutes(details['end']))
                if meeting_start < meeting_end:
                    score = meeting_end - meeting_start
                    if score > best_score:
                        best_score = score
                        best_meeting = (person, details, meeting_start, meeting_end)
        return best_meeting

    itinerary = []
    current_time = time_to_minutes(start_time)
    current_location = start_location
    visited = set()

    while True:
        best_meeting = find_best_meeting(current_time, current_location, visited)
        if not best_meeting:
            break
        person, details, meeting_start, meeting_end = best_meeting
        itinerary.append({
            "action": "meet",
            "location": details['location'],
            "person": person,
            "start_time": minutes_to_time(meeting_start),
            "end_time": minutes_to_time(meeting_end)
        })
        current_time = meeting_end
        current_location = details['location']
        visited.add(person)

    return itinerary

start_location = 'Sunset District'
start_time = '9:00'
itinerary = find_meeting_schedule(start_location, start_time, meetings, travel_times)

print(json.dumps({"itinerary": itinerary}, indent=4))