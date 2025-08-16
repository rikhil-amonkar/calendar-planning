import json
from datetime import datetime, timedelta

# Define travel times in minutes
travel_times = {
    ('Nob Hill', 'Pacific Heights'): 8,
    ('Nob Hill', 'Mission District'): 13,
    ('Pacific Heights', 'Nob Hill'): 8,
    ('Pacific Heights', 'Mission District'): 15,
    ('Mission District', 'Nob Hill'): 12,
    ('Mission District', 'Pacific Heights'): 16
}

# Define meeting constraints
meetings = {
    'Thomas': {'location': 'Pacific Heights', 'start': '15:30', 'end': '19:15', 'min_duration': 75},
    'Kenneth': {'location': 'Mission District', 'start': '12:00', 'end': '15:45', 'min_duration': 45}
}

# Start time
start_time = datetime.strptime('9:00', '%H:%M')

def parse_time(time_str):
    return datetime.strptime(time_str, '%H:%M')

def add_minutes(time, minutes):
    return time + timedelta(minutes=minutes)

def can_meet(start, end, min_duration):
    duration = (parse_time(end) - parse_time(start)).seconds // 60
    return duration >= min_duration

def find_schedule(start_time, meetings, travel_times):
    itinerary = []
    current_location = 'Nob Hill'
    current_time = start_time

    # Sort meetings by start time
    sorted_meetings = sorted(meetings.items(), key=lambda x: parse_time(x[1]['start']))

    for person, details in sorted_meetings:
        location = details['location']
        start = details['start']
        end = details['end']
        min_duration = details['min_duration']

        # Calculate travel time to the next meeting location
        travel_time = travel_times[(current_location, location)]

        # Check if we can reach the meeting location in time
        arrival_time = add_minutes(current_time, travel_time)
        if arrival_time > parse_time(end):
            continue

        # Adjust meeting start time if we arrive early
        meeting_start_time = max(arrival_time, parse_time(start))

        # Check if we can meet for the required duration
        if can_meet(meeting_start_time.strftime('%H:%M'), end, min_duration):
            meeting_end_time = add_minutes(meeting_start_time, min_duration)
            itinerary.append({
                "action": "meet",
                "location": location,
                "person": person,
                "start_time": meeting_start_time.strftime('%H:%M').replace(':00', ':0'),
                "end_time": meeting_end_time.strftime('%H:%M').replace(':00', ':0')
            })
            current_time = meeting_end_time
            current_location = location

    return itinerary

itinerary = find_schedule(start_time, meetings, travel_times)
result = {"itinerary": itinerary}
print(json.dumps(result))