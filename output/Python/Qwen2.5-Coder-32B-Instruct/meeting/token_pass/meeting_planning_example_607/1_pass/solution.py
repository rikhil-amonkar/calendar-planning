import json
from datetime import datetime, timedelta

# Define travel times as a dictionary of dictionaries
travel_times = {
    'Sunset District': {'Russian Hill': 24, 'The Castro': 17, 'Richmond District': 12, 'Marina District': 21, 'North Beach': 29, 'Union Square': 30, 'Golden Gate Park': 11},
    'Russian Hill': {'Sunset District': 23, 'The Castro': 21, 'Richmond District': 14, 'Marina District': 7, 'North Beach': 5, 'Union Square': 11, 'Golden Gate Park': 21},
    'The Castro': {'Sunset District': 17, 'Russian Hill': 18, 'Richmond District': 16, 'Marina District': 21, 'North Beach': 20, 'Union Square': 19, 'Golden Gate Park': 11},
    'Richmond District': {'Sunset District': 11, 'Russian Hill': 13, 'The Castro': 16, 'Marina District': 9, 'North Beach': 17, 'Union Square': 21, 'Golden Gate Park': 9},
    'Marina District': {'Sunset District': 19, 'Russian Hill': 8, 'The Castro': 22, 'Richmond District': 11, 'North Beach': 11, 'Union Square': 16, 'Golden Gate Park': 18},
    'North Beach': {'Sunset District': 27, 'Russian Hill': 4, 'The Castro': 22, 'Richmond District': 18, 'Marina District': 9, 'Union Square': 7, 'Golden Gate Park': 22},
    'Union Square': {'Sunset District': 26, 'Russian Hill': 13, 'The Castro': 19, 'Richmond District': 20, 'Marina District': 18, 'North Beach': 10, 'Golden Gate Park': 22},
    'Golden Gate Park': {'Sunset District': 10, 'Russian Hill': 19, 'The Castro': 13, 'Richmond District': 7, 'Marina District': 16, 'North Beach': 24, 'Union Square': 22}
}

# Define meeting constraints
constraints = {
    'Karen': {'location': 'Russian Hill', 'start': '20:45', 'end': '21:45', 'duration': 60},
    'Jessica': {'location': 'The Castro', 'start': '15:45', 'end': '19:30', 'duration': 60},
    'Matthew': {'location': 'Richmond District', 'start': '07:30', 'end': '15:15', 'duration': 15},
    'Michelle': {'location': 'Marina District', 'start': '10:30', 'end': '18:45', 'duration': 75},
    'Carol': {'location': 'North Beach', 'start': '12:00', 'end': '17:00', 'duration': 90},
    'Stephanie': {'location': 'Union Square', 'start': '10:45', 'end': '14:15', 'duration': 30},
    'Linda': {'location': 'Golden Gate Park', 'start': '10:45', 'end': '22:00', 'duration': 90}
}

def parse_time(time_str):
    return datetime.strptime(time_str, '%H:%M')

def add_minutes(time, minutes):
    return time + timedelta(minutes=minutes)

def get_feasible_slots(constraint):
    start = parse_time(constraint['start'])
    end = parse_time(constraint['end'])
    duration = constraint['duration']
    feasible_slots = []
    current_start = start
    while current_start + timedelta(minutes=duration) <= end:
        feasible_slots.append((current_start, add_minutes(current_start, duration)))
        current_start += timedelta(minutes=1)
    return feasible_slots

def find_schedule(constraints, travel_times):
    current_time = parse_time('09:00')
    current_location = 'Sunset District'
    itinerary = []

    # Sort constraints by earliest possible start time
    sorted_constraints = sorted(constraints.items(), key=lambda x: parse_time(x[1]['start']))

    for name, constraint in sorted_constraints:
        feasible_slots = get_feasible_slots(constraint)
        for slot_start, slot_end in feasible_slots:
            travel_time = travel_times[current_location][constraint['location']]
            if add_minutes(current_time, travel_time) <= slot_start:
                # We can reach the meeting on time
                current_time = slot_end
                current_location = constraint['location']
                itinerary.append({
                    "action": "meet",
                    "location": constraint['location'],
                    "person": name,
                    "start_time": slot_start.strftime('%H:%M'),
                    "end_time": slot_end.strftime('%H:%M')
                })
                break

    return itinerary

itinerary = find_schedule(constraints, travel_times)
result = {"itinerary": itinerary}
print(json.dumps(result, indent=2))