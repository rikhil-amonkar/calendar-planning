import json
from datetime import datetime, timedelta

# Define travel times
travel_times = {
    ('Russian Hill', 'Nob Hill'): 5,
    ('Russian Hill', 'Mission District'): 16,
    ('Russian Hill', 'Embarcadero'): 8,
    ('Nob Hill', 'Russian Hill'): 5,
    ('Nob Hill', 'Mission District'): 13,
    ('Nob Hill', 'Embarcadero'): 9,
    ('Mission District', 'Russian Hill'): 15,
    ('Mission District', 'Nob Hill'): 12,
    ('Mission District', 'Embarcadero'): 20,
    ('Embarcadero', 'Russian Hill'): 8,
    ('Embarcadero', 'Nob Hill'): 9,
    ('Embarcadero', 'Mission District'): 20
}

# Define meeting constraints
constraints = {
    'Patricia': {'location': 'Nob Hill', 'start': '18:30', 'end': '21:45', 'min_duration': 90},
    'Ashley': {'location': 'Mission District', 'start': '20:30', 'end': '21:15', 'min_duration': 45},
    'Timothy': {'location': 'Embarcadero', 'start': '9:45', 'end': '17:45', 'min_duration': 120}
}

def parse_time(time_str):
    return datetime.strptime(time_str, '%H:%M')

def can_meet(constraint, start_time):
    constraint_start = parse_time(constraint['start'])
    constraint_end = parse_time(constraint['end'])
    min_duration = constraint['min_duration']
    if start_time < constraint_start:
        start_time = constraint_start
    end_time = start_time + timedelta(minutes=min_duration)
    return end_time <= constraint_end

def find_schedule():
    current_time = parse_time('9:00')
    current_location = 'Russian Hill'
    itinerary = []

    # List of people to meet in the order of their constraints
    people_to_meet = ['Timothy', 'Patricia', 'Ashley']

    for person in people_to_meet:
        constraint = constraints[person]
        travel_time = travel_times[(current_location, constraint['location'])]
        meet_start = current_time + timedelta(minutes=travel_time)
        
        # Ensure meet_start is within the person's availability
        if meet_start < parse_time(constraint['start']):
            meet_start = parse_time(constraint['start'])
        
        meet_end = meet_start + timedelta(minutes=constraint['min_duration'])
        
        if can_meet(constraint, meet_start):
            itinerary.append({
                "action": "meet",
                "location": constraint['location'],
                "person": person,
                "start_time": meet_start.strftime('%H:%M'),
                "end_time": meet_end.strftime('%H:%M')
            })
            current_time = meet_end
            current_location = constraint['location']
        else:
            print(f"Cannot meet {person} within their constraints.")

    return itinerary

schedule = find_schedule()
print(json.dumps({"itinerary": schedule}))