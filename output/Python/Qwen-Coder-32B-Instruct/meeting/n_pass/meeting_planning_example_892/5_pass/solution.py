import json
from datetime import datetime, timedelta

# Define travel times
travel_times = {
    ('Marina District', 'Bayview'): 27,
    ('Marina District', 'Sunset District'): 19,
    ('Marina District', 'Richmond District'): 11,
    ('Marina District', 'Nob Hill'): 12,
    ('Marina District', 'Chinatown'): 15,
    ('Marina District', 'Haight-Ashbury'): 16,
    ('Marina District', 'North Beach'): 11,
    ('Marina District', 'Russian Hill'): 8,
    ('Marina District', 'Embarcadero'): 14,
    ('Bayview', 'Marina District'): 27,
    ('Bayview', 'Sunset District'): 23,
    ('Bayview', 'Richmond District'): 25,
    ('Bayview', 'Nob Hill'): 20,
    ('Bayview', 'Chinatown'): 19,
    ('Bayview', 'Haight-Ashbury'): 19,
    ('Bayview', 'North Beach'): 22,
    ('Bayview', 'Russian Hill'): 23,
    ('Bayview', 'Embarcadero'): 19,
    ('Sunset District', 'Marina District'): 21,
    ('Sunset District', 'Bayview'): 22,
    ('Sunset District', 'Richmond District'): 12,
    ('Sunset District', 'Nob Hill'): 27,
    ('Sunset District', 'Chinatown'): 30,
    ('Sunset District', 'Haight-Ashbury'): 15,
    ('Sunset District', 'North Beach'): 28,
    ('Sunset District', 'Russian Hill'): 24,
    ('Sunset District', 'Embarcadero'): 30,
    ('Richmond District', 'Marina District'): 9,
    ('Richmond District', 'Bayview'): 27,
    ('Richmond District', 'Sunset District'): 11,
    ('Richmond District', 'Nob Hill'): 17,
    ('Richmond District', 'Chinatown'): 20,
    ('Richmond District', 'Haight-Ashbury'): 10,
    ('Richmond District', 'North Beach'): 17,
    ('Richmond District', 'Russian Hill'): 13,
    ('Richmond District', 'Embarcadero'): 19,
    ('Nob Hill', 'Marina District'): 11,
    ('Nob Hill', 'Bayview'): 19,
    ('Nob Hill', 'Sunset District'): 24,
    ('Nob Hill', 'Richmond District'): 14,
    ('Nob Hill', 'Chinatown'): 6,
    ('Nob Hill', 'Haight-Ashbury'): 13,
    ('Nob Hill', 'North Beach'): 8,
    ('Nob Hill', 'Russian Hill'): 5,
    ('Nob Hill', 'Embarcadero'): 9,
    ('Chinatown', 'Marina District'): 12,
    ('Chinatown', 'Bayview'): 20,
    ('Chinatown', 'Sunset District'): 29,
    ('Chinatown', 'Richmond District'): 20,
    ('Chinatown', 'Nob Hill'): 9,
    ('Chinatown', 'Haight-Ashbury'): 19,
    ('Chinatown', 'North Beach'): 3,
    ('Chinatown', 'Russian Hill'): 7,
    ('Chinatown', 'Embarcadero'): 5,
    ('Haight-Ashbury', 'Marina District'): 17,
    ('Haight-Ashbury', 'Bayview'): 18,
    ('Haight-Ashbury', 'Sunset District'): 15,
    ('Haight-Ashbury', 'Richmond District'): 10,
    ('Haight-Ashbury', 'Nob Hill'): 15,
    ('Haight-Ashbury', 'Chinatown'): 19,
    ('Haight-Ashbury', 'North Beach'): 19,
    ('Haight-Ashbury', 'Russian Hill'): 17,
    ('Haight-Ashbury', 'Embarcadero'): 20,
    ('North Beach', 'Marina District'): 9,
    ('North Beach', 'Bayview'): 25,
    ('North Beach', 'Sunset District'): 27,
    ('North Beach', 'Richmond District'): 18,
    ('North Beach', 'Nob Hill'): 7,
    ('North Beach', 'Chinatown'): 6,
    ('North Beach', 'Haight-Ashbury'): 18,
    ('North Beach', 'Russian Hill'): 4,
    ('North Beach', 'Embarcadero'): 6,
    ('Russian Hill', 'Marina District'): 7,
    ('Russian Hill', 'Bayview'): 23,
    ('Russian Hill', 'Sunset District'): 23,
    ('Russian Hill', 'Richmond District'): 14,
    ('Russian Hill', 'Nob Hill'): 5,
    ('Russian Hill', 'Chinatown'): 9,
    ('Russian Hill', 'Haight-Ashbury'): 17,
    ('Russian Hill', 'North Beach'): 5,
    ('Russian Hill', 'Embarcadero'): 8,
    ('Embarcadero', 'Marina District'): 12,
    ('Embarcadero', 'Bayview'): 21,
    ('Embarcadero', 'Sunset District'): 30,
    ('Embarcadero', 'Richmond District'): 21,
    ('Embarcadero', 'Nob Hill'): 10,
    ('Embarcadero', 'Chinatown'): 7,
    ('Embarcadero', 'Haight-Ashbury'): 21,
    ('Embarcadero', 'North Beach'): 5,
    ('Embarcadero', 'Russian Hill'): 8,
}

# Define meeting constraints
meetings = {
    'Charles': {'location': 'Bayview', 'start': '11:30', 'end': '14:30', 'min_duration': 45},
    'Robert': {'location': 'Sunset District', 'start': '16:45', 'end': '21:00', 'min_duration': 30},
    'Karen': {'location': 'Richmond District', 'start': '19:15', 'end': '21:30', 'min_duration': 60},
    'Rebecca': {'location': 'Nob Hill', 'start': '16:15', 'end': '20:30', 'min_duration': 90},
    'Margaret': {'location': 'Chinatown', 'start': '14:15', 'end': '19:45', 'min_duration': 120},
    'Patricia': {'location': 'Haight-Ashbury', 'start': '14:30', 'end': '20:30', 'min_duration': 45},
    'Mark': {'location': 'North Beach', 'start': '14:00', 'end': '18:30', 'min_duration': 105},
    'Melissa': {'location': 'Russian Hill', 'start': '13:00', 'end': '19:45', 'min_duration': 30},
    'Laura': {'location': 'Embarcadero', 'start': '07:45', 'end': '13:15', 'min_duration': 105},
}

def parse_time(time_str):
    return datetime.strptime(time_str, '%H:%M')

def can_meet(start, end, min_duration, current_time):
    available_time = (parse_time(end) - parse_time(start)).total_seconds() / 60
    return available_time >= min_duration and current_time <= parse_time(start)

def find_next_meeting(current_location, current_time, scheduled_meetings):
    best_meeting = None
    best_travel_time = float('inf')
    for person, details in meetings.items():
        location = details['location']
        start = details['start']
        end = details['end']
        min_duration = details['min_duration']
        if person in scheduled_meetings:
            continue
        if can_meet(start, end, min_duration, current_time):
            travel_time = travel_times.get((current_location, location), float('inf'))
            meeting_start_time = max(current_time + timedelta(minutes=travel_time), parse_time(start))
            meeting_end_time = meeting_start_time + timedelta(minutes=min_duration)
            if meeting_end_time <= parse_time(end) and meeting_end_time <= parse_time('21:00'):
                if travel_time < best_travel_time:
                    best_meeting = (person, location, start, end, min_duration)
                    best_travel_time = travel_time
    return best_meeting, best_travel_time

def main():
    start_time = parse_time('9:00')
    current_time = start_time
    current_location = 'Marina District'
    itinerary = []
    scheduled_meetings = set()

    while True:
        next_meeting, travel_time = find_next_meeting(current_location, current_time, scheduled_meetings)
        if next_meeting is None:
            break
        person, location, start, end, min_duration = next_meeting
        meeting_start_time = max(current_time + timedelta(minutes=travel_time), parse_time(start))
        meeting_end_time = meeting_start_time + timedelta(minutes=min_duration)
        itinerary.append({
            "action": "meet",
            "location": location,
            "person": person,
            "start_time": meeting_start_time.strftime('%H:%M'),
            "end_time": meeting_end_time.strftime('%H:%M')
        })
        current_time = meeting_end_time
        current_location = location
        scheduled_meetings.add(person)

    print(json.dumps({"itinerary": itinerary}))

if __name__ == "__main__":
    main()