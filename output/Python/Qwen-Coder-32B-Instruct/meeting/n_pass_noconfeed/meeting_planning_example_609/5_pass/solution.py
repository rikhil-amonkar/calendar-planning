import json
from datetime import datetime, timedelta

# Define the travel times between locations (symmetric)
travel_times = {
    'Chinatown': {'Mission District': 18, 'Alamo Square': 17, 'Pacific Heights': 10, 'Union Square': 7, 'Golden Gate Park': 23, 'Sunset District': 29, 'Presidio': 19},
    'Mission District': {'Chinatown': 16, 'Alamo Square': 11, 'Pacific Heights': 16, 'Union Square': 15, 'Golden Gate Park': 17, 'Sunset District': 24, 'Presidio': 25},
    'Alamo Square': {'Chinatown': 16, 'Mission District': 10, 'Pacific Heights': 10, 'Union Square': 14, 'Golden Gate Park': 9, 'Sunset District': 16, 'Presidio': 18},
    'Pacific Heights': {'Chinatown': 11, 'Mission District': 15, 'Alamo Square': 10, 'Union Square': 12, 'Golden Gate Park': 15, 'Sunset District': 21, 'Presidio': 11},
    'Union Square': {'Chinatown': 7, 'Mission District': 14, 'Alamo Square': 15, 'Pacific Heights': 15, 'Golden Gate Park': 22, 'Sunset District': 26, 'Presidio': 24},
    'Golden Gate Park': {'Chinatown': 23, 'Mission District': 17, 'Alamo Square': 9, 'Pacific Heights': 15, 'Union Square': 22, 'Sunset District': 11, 'Presidio': 11},
    'Sunset District': {'Chinatown': 29, 'Mission District': 24, 'Alamo Square': 16, 'Pacific Heights': 21, 'Union Square': 26, 'Golden Gate Park': 11, 'Presidio': 16},
    'Presidio': {'Chinatown': 19, 'Mission District': 25, 'Alamo Square': 18, 'Pacific Heights': 11, 'Union Square': 24, 'Golden Gate Park': 11, 'Presidio': 15},
    # Add missing entries
    'Mission District': {'Mission District': 0, 'Golden Gate Park': 17, 'Alamo Square': 11, 'Pacific Heights': 16, 'Sunset District': 24},
    'Golden Gate Park': {'Golden Gate Park': 0, 'Mission District': 17, 'Alamo Square': 9, 'Pacific Heights': 15, 'Sunset District': 11},
    'Alamo Square': {'Alamo Square': 0, 'Mission District': 11, 'Golden Gate Park': 9, 'Pacific Heights': 10, 'Sunset District': 16},
    'Pacific Heights': {'Pacific Heights': 0, 'Mission District': 16, 'Golden Gate Park': 15, 'Alamo Square': 10, 'Sunset District': 21},
    'Sunset District': {'Sunset District': 0, 'Mission District': 24, 'Golden Gate Park': 11, 'Alamo Square': 16, 'Pacific Heights': 21}
}

# Define the meeting constraints
constraints = {
    'David': {'location': 'Mission District', 'start': '8:00', 'end': '19:45', 'min_duration': 45},
    'Kenneth': {'location': 'Alamo Square', 'start': '14:00', 'end': '19:45', 'min_duration': 120},
    'John': {'location': 'Pacific Heights', 'start': '17:00', 'end': '20:00', 'min_duration': 15},
    'Charles': {'location': 'Union Square', 'start': '21:45', 'end': '22:45', 'min_duration': 60},
    'Deborah': {'location': 'Golden Gate Park', 'start': '7:00', 'end': '18:15', 'min_duration': 90},
    'Karen': {'location': 'Sunset District', 'start': '17:45', 'end': '21:15', 'min_duration': 15},
    'Carol': {'location': 'Presidio', 'start': '8:15', 'end': '9:15', 'min_duration': 30}
}

def parse_time(time_str):
    return datetime.strptime(time_str, '%H:%M')

def add_minutes(time, minutes):
    return time + timedelta(minutes=minutes)

def time_to_str(time):
    return time.strftime('%H:%M')

def find_optimal_schedule(constraints, travel_times):
    start_time = parse_time('9:00')
    current_location = 'Chinatown'
    itinerary = []

    def can_meet(person, start_time):
        person_start = parse_time(constraints[person]['start'])
        person_end = parse_time(constraints[person]['end'])
        min_duration = constraints[person]['min_duration']
        available_time = (person_end - start_time).total_seconds() / 60
        return start_time >= person_start and available_time >= min_duration

    def find_next_meeting(start_time, current_location):
        best_person = None
        best_start_time = None
        best_end_time = None
        best_travel_time = None

        for person, details in constraints.items():
            if can_meet(person, start_time):
                location = details['location']
                try:
                    travel_time = travel_times[current_location][location]
                except KeyError as e:
                    print(f"KeyError: {e} - current_location: {current_location}, location: {location}")
                    continue
                person_start = parse_time(details['start'])
                person_end = parse_time(details['end'])
                min_duration = details['min_duration']

                # Calculate the earliest possible meeting time
                meeting_start_time = max(start_time, person_start)
                meeting_start_time = add_minutes(meeting_start_time, travel_time)
                meeting_end_time = add_minutes(meeting_start_time, min_duration)

                if meeting_end_time <= person_end and (best_travel_time is None or meeting_start_time < best_travel_time):
                    best_person = person
                    best_start_time = meeting_start_time
                    best_end_time = meeting_end_time
                    best_travel_time = meeting_start_time

        return best_person, best_start_time, best_end_time, best_travel_time

    while True:
        person, start_time, end_time, travel_time = find_next_meeting(start_time, current_location)
        if person is None:
            break

        itinerary.append({
            "action": "meet",
            "location": constraints[person]['location'],
            "person": person,
            "start_time": time_to_str(start_time),
            "end_time": time_to_str(end_time)
        })

        start_time = end_time
        current_location = constraints[person]['location']

    return itinerary

itinerary = find_optimal_schedule(constraints, travel_times)
result = {"itinerary": itinerary}
print(json.dumps(result, indent=4))