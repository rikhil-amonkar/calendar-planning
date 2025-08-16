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
    ('Mission District', 'Embarcadero'): 19,
    ('Embarcadero', 'Russian Hill'): 8,
    ('Embarcadero', 'Nob Hill'): 10,
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

def time_diff(start, end):
    return int((parse_time(end) - parse_time(start)).total_seconds() / 60)

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

    # Try to meet Timothy first since he has the longest window and earliest availability
    timothy_constraint = constraints['Timothy']
    if can_meet(timothy_constraint, current_time):
        travel_time = travel_times[(current_location, timothy_constraint['location'])]
        meet_start = current_time + timedelta(minutes=travel_time)
        meet_end = meet_start + timedelta(minutes=timothy_constraint['min_duration'])
        itinerary.append({
            "action": "meet",
            "location": timothy_constraint['location'],
            "person": "Timothy",
            "start_time": meet_start.strftime('%H:%M'),
            "end_time": meet_end.strftime('%H:%M')
        })
        current_time = meet_end
        current_location = timothy_constraint['location']

    # Try to meet Ashley next
    ashley_constraint = constraints['Ashley']
    if can_meet(ashley_constraint, current_time):
        travel_time = travel_times[(current_location, ashley_constraint['location'])]
        meet_start = current_time + timedelta(minutes=travel_time)
        meet_end = meet_start + timedelta(minutes=ashley_constraint['min_duration'])
        itinerary.append({
            "action": "meet",
            "location": ashley_constraint['location'],
            "person": "Ashley",
            "start_time": meet_start.strftime('%H:%M'),
            "end_time": meet_end.strftime('%H:%M')
        })
        current_time = meet_end
        current_location = ashley_constraint['location']

    # Finally, try to meet Patricia
    patricia_constraint = constraints['Patricia']
    if can_meet(patricia_constraint, current_time):
        travel_time = travel_times[(current_location, patricia_constraint['location'])]
        meet_start = current_time + timedelta(minutes=travel_time)
        meet_end = meet_start + timedelta(minutes=patricia_constraint['min_duration'])
        itinerary.append({
            "action": "meet",
            "location": patricia_constraint['location'],
            "person": "Patricia",
            "start_time": meet_start.strftime('%H:%M'),
            "end_time": meet_end.strftime('%H:%M')
        })

    return itinerary

schedule = find_schedule()
print(json.dumps({"itinerary": schedule}))