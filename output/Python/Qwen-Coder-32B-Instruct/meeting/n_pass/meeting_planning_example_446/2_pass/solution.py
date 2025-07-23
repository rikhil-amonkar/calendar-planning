import json
from datetime import datetime, timedelta

# Define travel times
travel_times = {
    ('Richmond District', 'Marina District'): 9,
    ('Richmond District', 'Chinatown'): 20,
    ('Richmond District', 'Financial District'): 22,
    ('Richmond District', 'Bayview'): 26,
    ('Richmond District', 'Union Square'): 21,
    ('Marina District', 'Richmond District'): 11,
    ('Marina District', 'Chinatown'): 16,
    ('Marina District', 'Financial District'): 17,
    ('Marina District', 'Bayview'): 27,
    ('Marina District', 'Union Square'): 16,
    ('Chinatown', 'Richmond District'): 20,
    ('Chinatown', 'Marina District'): 12,
    ('Chinatown', 'Financial District'): 5,
    ('Chinatown', 'Bayview'): 22,
    ('Chinatown', 'Union Square'): 7,
    ('Financial District', 'Richmond District'): 21,
    ('Financial District', 'Marina District'): 15,
    ('Financial District', 'Chinatown'): 5,
    ('Financial District', 'Bayview'): 19,
    ('Financial District', 'Union Square'): 9,
    ('Bayview', 'Richmond District'): 25,
    ('Bayview', 'Marina District'): 25,
    ('Bayview', 'Chinatown'): 18,
    ('Bayview', 'Financial District'): 19,
    ('Bayview', 'Union Square'): 17,
    ('Union Square', 'Richmond District'): 20,
    ('Union Square', 'Marina District'): 18,
    ('Union Square', 'Chinatown'): 7,
    ('Union Square', 'Financial District'): 9,
    ('Union Square', 'Bayview'): 15,
}

# Define meeting constraints
meetings = {
    'Kimberly': {'location': 'Marina District', 'start': '13:15', 'end': '16:45', 'min_duration': 15},
    'Robert': {'location': 'Chinatown', 'start': '12:15', 'end': '20:15', 'min_duration': 15},
    'Rebecca': {'location': 'Financial District', 'start': '13:15', 'end': '16:45', 'min_duration': 75},
    'Margaret': {'location': 'Bayview', 'start': '09:30', 'end': '13:30', 'min_duration': 30},
    'Kenneth': {'location': 'Union Square', 'start': '19:30', 'end': '21:15', 'min_duration': 75},
}

def parse_time(time_str):
    return datetime.strptime(time_str, '%H:%M')

def time_to_str(time_obj):
    return time_obj.strftime('%H:%M')

def can_meet(start, end, min_duration):
    return (end - start).total_seconds() / 60 >= min_duration

def find_optimal_schedule():
    start_time = parse_time('9:00')
    current_location = 'Richmond District'
    itinerary = []

    # Sort meetings by start time
    sorted_meetings = sorted(meetings.items(), key=lambda x: parse_time(x[1]['start']))

    for person, details in sorted_meetings:
        location = details['location']
        start = parse_time(details['start'])
        end = parse_time(details['end'])
        min_duration = details['min_duration']

        # Calculate travel time
        travel_time = travel_times.get((current_location, location), float('inf'))
        arrival_time = start_time + timedelta(minutes=travel_time)

        # Check if we can meet within the available time
        if arrival_time + timedelta(minutes=min_duration) <= end:
            meeting_start = max(arrival_time, start)
            meeting_end = meeting_start + timedelta(minutes=min_duration)
            
            # Ensure meeting does not exceed the end time
            if meeting_end > end:
                meeting_end = end
            
            itinerary.append({
                "action": "meet",
                "location": location,
                "person": person,
                "start_time": time_to_str(meeting_start),
                "end_time": time_to_str(meeting_end)
            })
            start_time = meeting_end
            current_location = location

    return itinerary

itinerary = find_optimal_schedule()
result = {"itinerary": itinerary}
print(json.dumps(result, indent=4))