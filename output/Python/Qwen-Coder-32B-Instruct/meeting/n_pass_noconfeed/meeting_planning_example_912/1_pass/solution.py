import json
from datetime import datetime, timedelta

# Define travel times
travel_times = {
    'Union Square': {'Presidio': 24, 'Alamo Square': 15, 'Marina District': 18, 'Financial District': 9, 'Nob Hill': 9, 'Sunset District': 27, 'Chinatown': 7, 'Russian Hill': 13, 'North Beach': 10, 'Haight-Ashbury': 18},
    'Presidio': {'Union Square': 22, 'Alamo Square': 19, 'Marina District': 11, 'Financial District': 23, 'Nob Hill': 18, 'Sunset District': 15, 'Chinatown': 21, 'Russian Hill': 14, 'North Beach': 18, 'Haight-Ashbury': 15},
    'Alamo Square': {'Union Square': 14, 'Presidio': 17, 'Marina District': 15, 'Financial District': 17, 'Nob Hill': 11, 'Sunset District': 16, 'Chinatown': 15, 'Russian Hill': 13, 'North Beach': 15, 'Haight-Ashbury': 5},
    'Marina District': {'Union Square': 16, 'Presidio': 10, 'Alamo Square': 15, 'Financial District': 17, 'Nob Hill': 12, 'Sunset District': 19, 'Chinatown': 15, 'Russian Hill': 8, 'North Beach': 11, 'Haight-Ashbury': 16},
    'Financial District': {'Union Square': 9, 'Presidio': 22, 'Alamo Square': 17, 'Marina District': 15, 'Nob Hill': 8, 'Sunset District': 30, 'Chinatown': 5, 'Russian Hill': 11, 'North Beach': 7, 'Haight-Ashbury': 19},
    'Nob Hill': {'Union Square': 7, 'Presidio': 17, 'Alamo Square': 11, 'Marina District': 11, 'Financial District': 9, 'Sunset District': 24, 'Chinatown': 6, 'Russian Hill': 5, 'North Beach': 8, 'Haight-Ashbury': 13},
    'Sunset District': {'Union Square': 30, 'Presidio': 16, 'Alamo Square': 17, 'Marina District': 21, 'Financial District': 30, 'Nob Hill': 27, 'Chinatown': 29, 'Russian Hill': 23, 'North Beach': 28, 'Haight-Ashbury': 15},
    'Chinatown': {'Union Square': 7, 'Presidio': 19, 'Alamo Square': 17, 'Marina District': 12, 'Financial District': 5, 'Nob Hill': 9, 'Sunset District': 29, 'Russian Hill': 7, 'North Beach': 3, 'Haight-Ashbury': 19},
    'Russian Hill': {'Union Square': 10, 'Presidio': 14, 'Alamo Square': 15, 'Marina District': 7, 'Financial District': 11, 'Nob Hill': 5, 'Sunset District': 23, 'Chinatown': 9, 'North Beach': 5, 'Haight-Ashbury': 17},
    'North Beach': {'Union Square': 7, 'Presidio': 17, 'Alamo Square': 16, 'Marina District': 9, 'Financial District': 8, 'Nob Hill': 7, 'Sunset District': 27, 'Chinatown': 6, 'Russian Hill': 4, 'Haight-Ashbury': 18},
    'Haight-Ashbury': {'Union Square': 19, 'Presidio': 15, 'Alamo Square': 5, 'Marina District': 17, 'Financial District': 21, 'Nob Hill': 15, 'Sunset District': 15, 'Chinatown': 19, 'Russian Hill': 17, 'North Beach': 19}
}

# Define meeting constraints
meetings = {
    'Kimberly': {'location': 'Presidio', 'start': '15:30', 'end': '16:00', 'min_duration': 15},
    'Elizabeth': {'location': 'Alamo Square', 'start': '19:15', 'end': '20:15', 'min_duration': 15},
    'Joshua': {'location': 'Marina District', 'start': '10:30', 'end': '14:15', 'min_duration': 45},
    'Sandra': {'location': 'Financial District', 'start': '19:30', 'end': '20:15', 'min_duration': 45},
    'Kenneth': {'location': 'Nob Hill', 'start': '12:45', 'end': '21:45', 'min_duration': 30},
    'Betty': {'location': 'Sunset District', 'start': '14:00', 'end': '19:00', 'min_duration': 60},
    'Deborah': {'location': 'Chinatown', 'start': '17:15', 'end': '20:30', 'min_duration': 15},
    'Barbara': {'location': 'Russian Hill', 'start': '17:30', 'end': '21:15', 'min_duration': 120},
    'Steven': {'location': 'North Beach', 'start': '17:45', 'end': '20:45', 'min_duration': 90},
    'Daniel': {'location': 'Haight-Ashbury', 'start': '18:30', 'end': '18:45', 'min_duration': 15}
}

def parse_time(time_str):
    return datetime.strptime(time_str, '%H:%M')

def add_minutes(time, minutes):
    return time + timedelta(minutes=minutes)

def can_meet(start, end, min_duration):
    return (end - start).total_seconds() / 60 >= min_duration

def find_best_schedule(meetings, travel_times):
    current_location = 'Union Square'
    current_time = parse_time('9:00')
    itinerary = []

    def find_next_meeting():
        best_meeting = None
        best_end_time = None
        for person, details in meetings.items():
            location = details['location']
            start = parse_time(details['start'])
            end = parse_time(details['end'])
            min_duration = details['min_duration']
            travel_time = travel_times[current_location][location]
            potential_start = max(current_time + timedelta(minutes=travel_time), start)
            potential_end = add_minutes(potential_start, min_duration)
            if can_meet(potential_start, end, min_duration) and (best_end_time is None or potential_end < best_end_time):
                best_meeting = (person, location, potential_start, potential_end)
                best_end_time = potential_end
        return best_meeting

    while True:
        next_meeting = find_next_meeting()
        if next_meeting is None:
            break
        person, location, start, end = next_meeting
        itinerary.append({
            "action": "meet",
            "location": location,
            "person": person,
            "start_time": start.strftime('%H:%M'),
            "end_time": end.strftime('%H:%M')
        })
        current_location = location
        current_time = end
        del meetings[person]

    return itinerary

itinerary = find_best_schedule(meetings.copy(), travel_times)
print(json.dumps({"itinerary": itinerary}, indent=2))