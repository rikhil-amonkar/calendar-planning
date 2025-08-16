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

def time_to_str(dt):
    return dt.strftime('%H:%M')

def find_optimal_schedule():
    start_time = parse_time('9:00')
    current_location = 'Nob Hill'
    itinerary = []

    # Sort meetings by start time
    sorted_meetings = sorted(meetings.items(), key=lambda x: parse_time(x[1]['start']))

    for name, meeting in sorted_meetings:
        location = meeting['location']
        start = parse_time(meeting['start'])
        end = parse_time(meeting['end'])
        min_duration = meeting['min_duration']

        # Calculate travel time to the meeting location
        travel_time = travel_times.get((current_location, location), float('inf'))

        # Calculate potential meeting start time
        potential_start = max(start_time + timedelta(minutes=travel_time), start)

        # Check if we can meet for the required duration
        if potential_start + timedelta(minutes=min_duration) <= end:
            # Add meeting to itinerary
            itinerary.append({
                "action": "meet",
                "location": location,
                "person": name,
                "start_time": time_to_str(potential_start),
                "end_time": time_to_str(potential_start + timedelta(minutes=min_duration))
            })

            # Update current time and location
            start_time = potential_start + timedelta(minutes=min_duration)
            current_location = location

    return itinerary

itinerary = find_optimal_schedule()
result = {"itinerary": itinerary}
print(json.dumps(result))