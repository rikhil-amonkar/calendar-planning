import json
from datetime import datetime, timedelta

# Define the travel times between locations
travel_times = {
    ('Financial District', 'Fisherman\'s Wharf'): 10,
    ('Financial District', 'Pacific Heights'): 13,
    ('Financial District', 'Mission District'): 17,
    ('Fisherman\'s Wharf', 'Financial District'): 11,
    ('Fisherman\'s Wharf', 'Pacific Heights'): 12,
    ('Fisherman\'s Wharf', 'Mission District'): 22,
    ('Pacific Heights', 'Financial District'): 13,
    ('Pacific Heights', 'Fisherman\'s Wharf'): 13,
    ('Pacific Heights', 'Mission District'): 15,
    ('Mission District', 'Financial District'): 17,
    ('Mission District', 'Fisherman\'s Wharf'): 22,
    ('Mission District', 'Pacific Heights'): 16
}

# Define the meeting constraints
constraints = {
    'David': {'location': 'Fisherman\'s Wharf', 'start': '10:45', 'end': '15:30', 'min_duration': 15},
    'Timothy': {'location': 'Pacific Heights', 'start': '09:00', 'end': '15:30', 'min_duration': 75},
    'Robert': {'location': 'Mission District', 'start': '12:15', 'end': '19:45', 'min_duration': 90}
}

def parse_time(time_str):
    return datetime.strptime(time_str, '%H:%M')

def format_time(dt):
    return dt.strftime('%H:%M')

def calculate_schedule(start_location, start_time):
    current_location = start_location
    current_time = parse_time(start_time)
    itinerary = []

    def can_meet(constraint, start_time):
        constraint_start = parse_time(constraint['start'])
        constraint_end = parse_time(constraint['end'])
        min_duration = timedelta(minutes=constraint['min_duration'])
        meeting_end = start_time + min_duration
        return start_time >= constraint_start and meeting_end <= constraint_end

    # Sort constraints by start time to try earliest meetings first
    sorted_constraints = sorted(constraints.items(), key=lambda x: parse_time(x[1]['start']))

    for name, constraint in sorted_constraints:
        travel_time = travel_times.get((current_location, constraint['location']), float('inf'))
        potential_start = current_time + timedelta(minutes=travel_time)

        if can_meet(constraint, potential_start):
            meeting_start = potential_start
            meeting_end = meeting_start + timedelta(minutes=constraint['min_duration'])
            itinerary.append({
                "action": "meet",
                "location": constraint['location'],
                "person": name,
                "start_time": format_time(meeting_start),
                "end_time": format_time(meeting_end)
            })
            current_location = constraint['location']
            current_time = meeting_end

    return itinerary

# Generate the schedule
schedule = calculate_schedule('Financial District', '09:00')
result = {"itinerary": schedule}

# Output the result as JSON
print(json.dumps(result, indent=2))