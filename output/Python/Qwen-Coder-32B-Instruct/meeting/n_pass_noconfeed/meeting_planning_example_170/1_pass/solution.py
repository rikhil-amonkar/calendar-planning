import json
from datetime import datetime, timedelta

# Define travel times in minutes
travel_times = {
    ('North Beach', 'Union Square'): 7,
    ('North Beach', 'Russian Hill'): 4,
    ('Union Square', 'North Beach'): 10,
    ('Union Square', 'Russian Hill'): 13,
    ('Russian Hill', 'North Beach'): 5,
    ('Russian Hill', 'Union Square'): 11
}

# Define meeting constraints
constraints = {
    'Emily': {'location': 'Union Square', 'start': '16:00', 'end': '17:15', 'min_duration': 45},
    'Margaret': {'location': 'Russian Hill', 'start': '19:00', 'end': '21:00', 'min_duration': 120}
}

def parse_time(time_str):
    return datetime.strptime(time_str, '%H:%M')

def format_time(time_obj):
    return time_obj.strftime('%H:%M').lstrip('0')

def calculate_schedule(constraints, travel_times):
    start_time = parse_time('9:00')
    current_location = 'North Beach'
    itinerary = []

    def can_meet(start, end, min_duration):
        duration = (parse_time(end) - parse_time(start)).total_seconds() / 60
        return duration >= min_duration

    def add_meeting(person, location, start, end):
        itinerary.append({
            "action": "meet",
            "location": location,
            "person": person,
            "start_time": format_time(parse_time(start)),
            "end_time": format_time(parse_time(end))
        })

    # Check if we can meet Emily
    emily_start = parse_time(constraints['Emily']['start'])
    emily_end = parse_time(constraints['Emily']['end'])
    emily_min_duration = constraints['Emily']['min_duration']

    # Calculate time to get to Union Square
    travel_to_union_square = travel_times[(current_location, 'Union Square')]
    potential_emily_start = start_time + timedelta(minutes=travel_to_union_square)

    if potential_emily_start <= emily_start:
        if can_meet(format_time(emily_start), constraints['Emily']['end'], emily_min_duration):
            add_meeting('Emily', 'Union Square', format_time(emily_start), constraints['Emily']['end'])
            current_location = 'Union Square'
            start_time = emily_end

    # Check if we can meet Margaret
    margaret_start = parse_time(constraints['Margaret']['start'])
    margaret_end = parse_time(constraints['Margaret']['end'])
    margaret_min_duration = constraints['Margaret']['min_duration']

    # Calculate time to get to Russian Hill from current location
    travel_to_russian_hill = travel_times[(current_location, 'Russian Hill')]
    potential_margaret_start = start_time + timedelta(minutes=travel_to_russian_hill)

    if potential_margaret_start <= margaret_start:
        if can_meet(format_time(margaret_start), constraints['Margaret']['end'], margaret_min_duration):
            add_meeting('Margaret', 'Russian Hill', format_time(margaret_start), constraints['Margaret']['end'])

    return itinerary

itinerary = calculate_schedule(constraints, travel_times)
output = {"itinerary": itinerary}
print(json.dumps(output))