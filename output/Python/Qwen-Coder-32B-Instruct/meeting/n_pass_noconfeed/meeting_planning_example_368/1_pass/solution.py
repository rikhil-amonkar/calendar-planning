import json
from datetime import datetime, timedelta

# Define travel times
travel_times = {
    ('Bayview', 'Russian Hill'): 23,
    ('Bayview', 'Alamo Square'): 16,
    ('Bayview', 'North Beach'): 21,
    ('Bayview', 'Financial District'): 19,
    ('Russian Hill', 'Bayview'): 23,
    ('Russian Hill', 'Alamo Square'): 15,
    ('Russian Hill', 'North Beach'): 5,
    ('Russian Hill', 'Financial District'): 11,
    ('Alamo Square', 'Bayview'): 16,
    ('Alamo Square', 'Russian Hill'): 13,
    ('Alamo Square', 'North Beach'): 15,
    ('Alamo Square', 'Financial District'): 17,
    ('North Beach', 'Bayview'): 22,
    ('North Beach', 'Russian Hill'): 4,
    ('North Beach', 'Alamo Square'): 16,
    ('North Beach', 'Financial District'): 8,
    ('Financial District', 'Bayview'): 19,
    ('Financial District', 'Russian Hill'): 10,
    ('Financial District', 'Alamo Square'): 17,
    ('Financial District', 'North Beach'): 7,
}

# Define meeting constraints
constraints = {
    'Joseph': {'location': 'Russian Hill', 'start': '8:30', 'end': '19:15', 'min_duration': 60},
    'Nancy': {'location': 'Alamo Square', 'start': '11:00', 'end': '16:00', 'min_duration': 90},
    'Jason': {'location': 'North Beach', 'start': '16:45', 'end': '21:45', 'min_duration': 15},
    'Jeffrey': {'location': 'Financial District', 'start': '10:30', 'end': '15:45', 'min_duration': 45},
}

def parse_time(time_str):
    return datetime.strptime(time_str, '%H:%M')

def time_to_str(time_obj):
    return time_obj.strftime('%H:%M')

def find_meeting_schedule():
    start_time = parse_time('9:00')
    current_location = 'Bayview'
    itinerary = []

    def can_meet(person, current_time):
        constraint = constraints[person]
        person_start = parse_time(constraint['start'])
        person_end = parse_time(constraint['end'])
        return person_start <= current_time < person_end - timedelta(minutes=constraint['min_duration'])

    def next_location(current_time, current_loc):
        options = []
        for person, constraint in constraints.items():
            if can_meet(person, current_time):
                travel_time = travel_times[(current_loc, constraint['location'])]
                meet_start = current_time + timedelta(minutes=travel_time)
                meet_end = meet_start + timedelta(minutes=constraint['min_duration'])
                if parse_time(constraint['end']) >= meet_end:
                    options.append((person, meet_start, meet_end))
        return sorted(options, key=lambda x: x[1])

    while start_time < parse_time('19:15'):
        options = next_location(start_time, current_location)
        if not options:
            break
        best_option = options[0]
        person, meet_start, meet_end = best_option
        itinerary.append({
            "action": "meet",
            "location": constraints[person]['location'],
            "person": person,
            "start_time": time_to_str(meet_start),
            "end_time": time_to_str(meet_end)
        })
        start_time = meet_end
        current_location = constraints[person]['location']

    return itinerary

itinerary = find_meeting_schedule()
result = {"itinerary": itinerary}
print(json.dumps(result))