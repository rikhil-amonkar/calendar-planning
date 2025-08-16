import json
from datetime import datetime, timedelta

# Define the travel times between locations
travel_times = {
    ('Pacific Heights', 'Nob Hill'): 8,
    ('Pacific Heights', 'Russian Hill'): 7,
    ('Pacific Heights', 'The Castro'): 16,
    ('Pacific Heights', 'Sunset District'): 21,
    ('Pacific Heights', 'Haight-Ashbury'): 11,
    ('Nob Hill', 'Pacific Heights'): 8,
    ('Nob Hill', 'Russian Hill'): 5,
    ('Nob Hill', 'The Castro'): 17,
    ('Nob Hill', 'Sunset District'): 25,
    ('Nob Hill', 'Haight-Ashbury'): 13,
    ('Russian Hill', 'Pacific Heights'): 7,
    ('Russian Hill', 'Nob Hill'): 5,
    ('Russian Hill', 'The Castro'): 21,
    ('Russian Hill', 'Sunset District'): 23,
    ('Russian Hill', 'Haight-Ashbury'): 17,
    ('The Castro', 'Pacific Heights'): 16,
    ('The Castro', 'Nob Hill'): 16,
    ('The Castro', 'Russian Hill'): 18,
    ('The Castro', 'Sunset District'): 17,
    ('The Castro', 'Haight-Ashbury'): 6,
    ('Sunset District', 'Pacific Heights'): 21,
    ('Sunset District', 'Nob Hill'): 27,
    ('Sunset District', 'Russian Hill'): 24,
    ('Sunset District', 'The Castro'): 17,
    ('Sunset District', 'Haight-Ashbury'): 15,
    ('Haight-Ashbury', 'Pacific Heights'): 12,
    ('Haight-Ashbury', 'Nob Hill'): 15,
    ('Haight-Ashbury', 'Russian Hill'): 17,
    ('Haight-Ashbury', 'The Castro'): 6,
    ('Haight-Ashbury', 'Sunset District'): 15,
}

# Define the meeting constraints
meetings = {
    'Ronald': {'location': 'Nob Hill', 'start': '10:00', 'end': '17:00', 'min_duration': 105},
    'Sarah': {'location': 'Russian Hill', 'start': '7:15', 'end': '9:30', 'min_duration': 45},
    'Helen': {'location': 'The Castro', 'start': '13:30', 'end': '17:00', 'min_duration': 120},
    'Joshua': {'location': 'Sunset District', 'start': '14:15', 'end': '19:30', 'min_duration': 90},
    'Margaret': {'location': 'Haight-Ashbury', 'start': '10:15', 'end': '22:00', 'min_duration': 60},
}

def parse_time(time_str):
    return datetime.strptime(time_str, '%H:%M')

def time_to_str(time_obj):
    return time_obj.strftime('%H:%M')

def find_meeting_schedule():
    start_time = parse_time('9:00')
    current_location = 'Pacific Heights'
    itinerary = []

    def can_meet(person, current_time):
        meeting = meetings[person]
        meeting_start = parse_time(meeting['start'])
        meeting_end = parse_time(meeting['end'])
        min_duration = meeting['min_duration']
        available_start = max(current_time, meeting_start)
        available_end = min(meeting_end, start_time + timedelta(hours=12))  # Assuming a 12-hour window
        return (available_end - available_start).total_seconds() / 60 >= min_duration

    def next_meeting(current_time, current_location):
        for person, details in meetings.items():
            if can_meet(person, current_time):
                meeting_start = parse_time(details['start'])
                meeting_end = parse_time(details['end'])
                travel_time = travel_times[(current_location, details['location'])]
                arrival_time = current_time + timedelta(minutes=travel_time)
                meeting_start_time = max(arrival_time, meeting_start)
                meeting_end_time = meeting_start_time + timedelta(minutes=details['min_duration'])
                if meeting_end_time <= meeting_end:
                    return person, meeting_start_time, meeting_end_time
        return None, None, None

    while True:
        person, meeting_start, meeting_end = next_meeting(start_time, current_location)
        if person is None:
            break
        travel_time = travel_times[(current_location, meetings[person]['location'])]
        start_time += timedelta(minutes=travel_time)
        itinerary.append({
            "action": "meet",
            "location": meetings[person]['location'],
            "person": person,
            "start_time": time_to_str(start_time),
            "end_time": time_to_str(meeting_end)
        })
        start_time = meeting_end
        current_location = meetings[person]['location']

    return itinerary

itinerary = find_meeting_schedule()
result = {"itinerary": itinerary}
print(json.dumps(result))