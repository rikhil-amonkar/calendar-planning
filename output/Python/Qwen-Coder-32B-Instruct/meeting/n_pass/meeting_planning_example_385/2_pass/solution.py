import json
from datetime import datetime, timedelta

# Define travel times
travel_times = {
    ('Nob Hill', 'Presidio'): 17,
    ('Nob Hill', 'North Beach'): 8,
    ('Nob Hill', 'Fisherman\'s Wharf'): 11,
    ('Nob Hill', 'Pacific Heights'): 8,
    ('Presidio', 'Nob Hill'): 18,
    ('Presidio', 'North Beach'): 18,
    ('Presidio', 'Fisherman\'s Wharf'): 19,
    ('Presidio', 'Pacific Heights'): 11,
    ('North Beach', 'Nob Hill'): 7,
    ('North Beach', 'Presidio'): 17,
    ('North Beach', 'Fisherman\'s Wharf'): 5,
    ('North Beach', 'Pacific Heights'): 8,
    ('Fisherman\'s Wharf', 'Nob Hill'): 11,
    ('Fisherman\'s Wharf', 'Presidio'): 17,
    ('Fisherman\'s Wharf', 'North Beach'): 6,
    ('Fisherman\'s Wharf', 'Pacific Heights'): 12,
    ('Pacific Heights', 'Nob Hill'): 8,
    ('Pacific Heights', 'Presidio'): 11,
    ('Pacific Heights', 'North Beach'): 9,
    ('Pacific Heights', 'Fisherman\'s Wharf'): 13
}

# Define meeting constraints
constraints = {
    'Jeffrey': {'location': 'Presidio', 'start': '8:00', 'end': '10:00', 'min_duration': 105},
    'Steven': {'location': 'North Beach', 'start': '13:30', 'end': '22:00', 'min_duration': 45},
    'Barbara': {'location': 'Fisherman\'s Wharf', 'start': '18:00', 'end': '21:30', 'min_duration': 30},
    'John': {'location': 'Pacific Heights', 'start': '9:00', 'end': '13:30', 'min_duration': 15}
}

def parse_time(time_str):
    return datetime.strptime(time_str, '%H:%M')

def add_minutes(time, minutes):
    return time + timedelta(minutes=minutes)

def time_to_str(time):
    return time.strftime('%H:%M')

def find_meeting_time(constraint, current_time):
    start = max(parse_time(constraint['start']), current_time)
    end = parse_time(constraint['end'])
    duration = constraint['min_duration']
    
    if add_minutes(start, duration) <= end:
        return start, add_minutes(start, duration)
    return None, None

def calculate_schedule():
    current_time = parse_time('9:00')
    itinerary = []
    locations = ['Nob Hill', 'Presidio', 'North Beach', 'Fisherman\'s Wharf', 'Pacific Heights']
    visited = set()
    
    # Sort constraints by their earliest possible meeting start time
    sorted_constraints = sorted(constraints.items(), key=lambda x: parse_time(x[1]['start']))
    
    current_location = 'Nob Hill'
    
    for person, constraint in sorted_constraints:
        if person in visited:
            continue
        
        # Find the meeting time within the constraints
        start, end = find_meeting_time(constraint, current_time)
        if not start or not end:
            continue
        
        # Calculate travel time to the meeting location
        travel_time = travel_times.get((current_location, constraint['location']), float('inf'))
        travel_end_time = add_minutes(current_time, travel_time)
        
        # If the travel end time is before the meeting start time, add travel action
        if travel_end_time < start:
            itinerary.append({
                "action": "travel",
                "location": constraint['location'],
                "person": None,
                "start_time": time_to_str(current_time),
                "end_time": time_to_str(travel_end_time)
            })
            current_time = travel_end_time
            current_location = constraint['location']
        
        # Add the meeting action
        itinerary.append({
            "action": "meet",
            "location": constraint['location'],
            "person": person,
            "start_time": time_to_str(start),
            "end_time": time_to_str(end)
        })
        
        current_time = end
        visited.add(person)
    
    return itinerary

schedule = calculate_schedule()
print(json.dumps({"itinerary": schedule}, indent=2))