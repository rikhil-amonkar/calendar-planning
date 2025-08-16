import json
from datetime import datetime, timedelta

# Define travel times
travel_times = {
    ('Russian Hill', 'Presidio'): 14,
    ('Russian Hill', 'Chinatown'): 9,
    ('Russian Hill', 'Pacific Heights'): 7,
    ('Russian Hill', 'Richmond District'): 14,
    ('Russian Hill', 'Fisherman\'s Wharf'): 7,
    ('Russian Hill', 'Golden Gate Park'): 21,
    ('Russian Hill', 'Bayview'): 23,
    ('Presidio', 'Russian Hill'): 14,
    ('Presidio', 'Chinatown'): 21,
    ('Presidio', 'Pacific Heights'): 11,
    ('Presidio', 'Richmond District'): 7,
    ('Presidio', 'Fisherman\'s Wharf'): 19,
    ('Presidio', 'Golden Gate Park'): 12,
    ('Presidio', 'Bayview'): 31,
    ('Chinatown', 'Russian Hill'): 7,
    ('Chinatown', 'Presidio'): 19,
    ('Chinatown', 'Pacific Heights'): 10,
    ('Chinatown', 'Richmond District'): 20,
    ('Chinatown', 'Fisherman\'s Wharf'): 8,
    ('Chinatown', 'Golden Gate Park'): 23,
    ('Chinatown', 'Bayview'): 22,
    ('Pacific Heights', 'Russian Hill'): 7,
    ('Pacific Heights', 'Presidio'): 11,
    ('Pacific Heights', 'Chinatown'): 10,
    ('Pacific Heights', 'Richmond District'): 12,
    ('Pacific Heights', 'Fisherman\'s Wharf'): 13,
    ('Pacific Heights', 'Golden Gate Park'): 15,
    ('Pacific Heights', 'Bayview'): 22,
    ('Richmond District', 'Russian Hill'): 14,
    ('Richmond District', 'Presidio'): 7,
    ('Richmond District', 'Chinatown'): 20,
    ('Richmond District', 'Pacific Heights'): 10,
    ('Richmond District', 'Fisherman\'s Wharf'): 18,
    ('Richmond District', 'Golden Gate Park'): 9,
    ('Richmond District', 'Bayview'): 26,
    ('Fisherman\'s Wharf', 'Russian Hill'): 7,
    ('Fisherman\'s Wharf', 'Presidio'): 17,
    ('Fisherman\'s Wharf', 'Chinatown'): 12,
    ('Fisherman\'s Wharf', 'Pacific Heights'): 12,
    ('Fisherman\'s Wharf', 'Richmond District'): 18,
    ('Fisherman\'s Wharf', 'Golden Gate Park'): 25,
    ('Fisherman\'s Wharf', 'Bayview'): 26,
    ('Golden Gate Park', 'Russian Hill'): 19,
    ('Golden Gate Park', 'Presidio'): 11,
    ('Golden Gate Park', 'Chinatown'): 23,
    ('Golden Gate Park', 'Pacific Heights'): 15,
    ('Golden Gate Park', 'Richmond District'): 7,
    ('Golden Gate Park', 'Fisherman\'s Wharf'): 24,
    ('Golden Gate Park', 'Bayview'): 23,
    ('Bayview', 'Russian Hill'): 23,
    ('Bayview', 'Presidio'): 31,
    ('Bayview', 'Chinatown'): 18,
    ('Bayview', 'Pacific Heights'): 23,
    ('Bayview', 'Richmond District'): 25,
    ('Bayview', 'Fisherman\'s Wharf'): 25,
    ('Bayview', 'Golden Gate Park'): 22,
}

# Define meeting constraints
meetings = {
    'Matthew': {'location': 'Presidio', 'start': '11:00', 'end': '21:00', 'min_duration': 90},
    'Margaret': {'location': 'Chinatown', 'start': '9:15', 'end': '18:45', 'min_duration': 90},
    'Nancy': {'location': 'Pacific Heights', 'start': '14:15', 'end': '17:00', 'min_duration': 15},
    'Helen': {'location': 'Richmond District', 'start': '19:45', 'end': '22:00', 'min_duration': 60},
    'Rebecca': {'location': 'Fisherman\'s Wharf', 'start': '21:15', 'end': '22:15', 'min_duration': 60},
    'Kimberly': {'location': 'Golden Gate Park', 'start': '13:00', 'end': '16:30', 'min_duration': 120},
    'Kenneth': {'location': 'Bayview', 'start': '14:30', 'end': '18:00', 'min_duration': 60},
}

def parse_time(time_str):
    return datetime.strptime(time_str, '%H:%M')

def time_to_str(time_obj):
    return time_obj.strftime('%H:%M')

def find_schedule():
    current_time = parse_time('9:00')
    current_location = 'Russian Hill'
    itinerary = []

    def can_meet(person, start, end, min_duration):
        person_start = parse_time(meetings[person]['start'])
        person_end = parse_time(meetings[person]['end'])
        available_start = max(start, person_start)
        available_end = min(end, person_end)
        return (available_end - available_start).total_seconds() / 60 >= min_duration

    def find_next_meeting(current_time, current_location):
        best_person = None
        best_start = None
        best_end = None
        best_travel_time = float('inf')

        for person, details in meetings.items():
            if any(meeting['person'] == person for meeting in itinerary):
                continue
            person_start = parse_time(details['start'])
            person_end = parse_time(details['end'])
            min_duration = details['min_duration']
            location = details['location']

            if can_meet(person, current_time, person_end, min_duration):
                travel_time = travel_times.get((current_location, location), float('inf'))
                meet_start = max(current_time + timedelta(minutes=travel_time), person_start)
                meet_end = meet_start + timedelta(minutes=min_duration)

                if meet_end <= person_end and travel_time < best_travel_time:
                    best_person = person
                    best_start = meet_start
                    best_end = meet_end
                    best_travel_time = travel_time

        return best_person, best_start, best_end

    while True:
        person, start, end = find_next_meeting(current_time, current_location)
        if person is None:
            break

        travel_time = travel_times[(current_location, meetings[person]['location'])]
        current_time += timedelta(minutes=travel_time)
        current_location = meetings[person]['location']

        # Check if the travel time fits within the available time before the meeting starts
        if current_time > start:
            continue

        itinerary.append({
            "action": "meet",
            "location": current_location,
            "person": person,
            "start_time": time_to_str(start),
            "end_time": time_to_str(end)
        })

        current_time = end

    return itinerary

itinerary = find_schedule()
result = {"itinerary": itinerary}
print(json.dumps(result, indent=4))