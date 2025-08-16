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
    'Margaret': {'location': 'Bayview', 'start': '9:30', 'end': '13:30', 'min_duration': 30},
    'Kenneth': {'location': 'Union Square', 'start': '19:30', 'end': '21:15', 'min_duration': 75},
}

def parse_time(time_str):
    return datetime.strptime(time_str, '%H:%M')

def time_to_str(dt):
    return dt.strftime('%H:%M')

def can_meet(start, end, min_duration):
    return (parse_time(end) - parse_time(start)).total_seconds() / 60 >= min_duration

def find_schedule():
    current_time = parse_time('9:00')
    location = 'Richmond District'
    itinerary = []

    # Sort meetings by earliest start time
    sorted_meetings = sorted(meetings.items(), key=lambda x: parse_time(x[1]['start']))

    for person, details in sorted_meetings:
        meeting_start = parse_time(details['start'])
        meeting_end = parse_time(details['end'])
        min_duration = details['min_duration']
        meeting_location = details['location']

        # Calculate travel time to next meeting location
        travel_time = travel_times[(location, meeting_location)]

        # Check if we can reach the meeting on time
        arrival_time = current_time + timedelta(minutes=travel_time)

        # Adjust arrival time if we arrive before meeting starts
        if arrival_time < meeting_start:
            arrival_time = meeting_start

        # Check if we can meet for the required duration
        if can_meet(time_to_str(arrival_time), details['end'], min_duration):
            meeting_end_time = arrival_time + timedelta(minutes=min_duration)
            if meeting_end_time <= meeting_end:
                itinerary.append({
                    "action": "meet",
                    "location": meeting_location,
                    "person": person,
                    "start_time": time_to_str(arrival_time),
                    "end_time": time_to_str(meeting_end_time)
                })
                current_time = meeting_end_time
                location = meeting_location

    return itinerary

itinerary = find_schedule()
result = {"itinerary": itinerary}
print(json.dumps(result))