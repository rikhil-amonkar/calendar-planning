import json
from datetime import datetime, timedelta

# Define travel times
travel_times = {
    ('Bayview', 'Pacific Heights'): 23,
    ('Bayview', 'Mission District'): 13,
    ('Bayview', 'Haight-Ashbury'): 19,
    ('Bayview', 'Financial District'): 19,
    ('Pacific Heights', 'Bayview'): 22,
    ('Pacific Heights', 'Mission District'): 15,
    ('Pacific Heights', 'Haight-Ashbury'): 11,
    ('Pacific Heights', 'Financial District'): 13,
    ('Mission District', 'Bayview'): 15,
    ('Mission District', 'Pacific Heights'): 16,
    ('Mission District', 'Haight-Ashbury'): 12,
    ('Mission District', 'Financial District'): 17,
    ('Haight-Ashbury', 'Bayview'): 18,
    ('Haight-Ashbury', 'Pacific Heights'): 12,
    ('Haight-Ashbury', 'Mission District'): 11,
    ('Haight-Ashbury', 'Financial District'): 21,
    ('Financial District', 'Bayview'): 19,
    ('Financial District', 'Pacific Heights'): 13,
    ('Financial District', 'Mission District'): 17,
    ('Financial District', 'Haight-Ashbury'): 19,
}

# Define meeting constraints
constraints = {
    'Mary': {'location': 'Pacific Heights', 'start': '10:00', 'end': '19:00', 'min_duration': 45},
    'Lisa': {'location': 'Mission District', 'start': '20:30', 'end': '22:00', 'min_duration': 75},
    'Betty': {'location': 'Haight-Ashbury', 'start': '07:15', 'end': '17:15', 'min_duration': 90},
    'Charles': {'location': 'Financial District', 'start': '11:15', 'end': '15:00', 'min_duration': 120},
}

def parse_time(time_str):
    return datetime.strptime(time_str, '%H:%M')

def add_minutes(time_obj, minutes):
    return time_obj + timedelta(minutes=minutes)

def can_meet(start, end, min_duration):
    return (end - start).total_seconds() / 60 >= min_duration

def find_schedule():
    current_time = parse_time('9:00')
    location = 'Bayview'
    itinerary = []

    def try_meeting(person, constraint):
        nonlocal current_time, location
        person_start = parse_time(constraint['start'])
        person_end = parse_time(constraint['end'])
        min_duration = constraint['min_duration']
        travel_time = travel_times[(location, constraint['location'])]
        
        # Calculate potential meeting start and end times
        potential_start = max(current_time + timedelta(minutes=travel_time), person_start)
        potential_end = min(potential_start + timedelta(minutes=min_duration), person_end)
        
        if can_meet(potential_start, potential_end, min_duration):
            itinerary.append({
                "action": "meet",
                "location": constraint['location'],
                "person": person,
                "start_time": potential_start.strftime('%H:%M'),
                "end_time": potential_end.strftime('%H:%M')
            })
            current_time = potential_end
            location = constraint['location']

    # Prioritize meetings based on constraints and availability
    try_meeting('Betty', constraints['Betty'])
    try_meeting('Charles', constraints['Charles'])
    try_meeting('Mary', constraints['Mary'])
    try_meeting('Lisa', constraints['Lisa'])

    return itinerary

itinerary = find_schedule()
output = {"itinerary": itinerary}
print(json.dumps(output))