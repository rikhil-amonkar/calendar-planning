import json
from datetime import datetime, timedelta

# Define travel times
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

# Define meeting constraints
meetings = {
    'David': {'location': 'Fisherman\'s Wharf', 'start': '10:45', 'end': '15:30', 'min_duration': 15},
    'Timothy': {'location': 'Pacific Heights', 'start': '9:00', 'end': '15:30', 'min_duration': 75},
    'Robert': {'location': 'Mission District', 'start': '12:15', 'end': '19:45', 'min_duration': 90}
}

def parse_time(time_str):
    return datetime.strptime(time_str, '%H:%M')

def add_minutes(time_obj, minutes):
    return time_obj + timedelta(minutes=minutes)

def can_meet(start, end, min_duration):
    return (parse_time(end) - parse_time(start)).total_seconds() / 60 >= min_duration

def find_schedule():
    current_time = parse_time('9:00')
    itinerary = []
    visited = set()

    def visit(location, person, start, end, min_duration):
        nonlocal current_time
        travel_time = travel_times.get(('Financial District', location), 0) if not itinerary else travel_times.get((itinerary[-1]['location'], location), 0)
        arrival_time = add_minutes(current_time, travel_time)
        meeting_start = max(arrival_time, parse_time(start))
        meeting_end = min(add_minutes(meeting_start, min_duration), parse_time(end))
        
        if can_meet(meeting_start.strftime('%H:%M'), meeting_end.strftime('%H:%M'), min_duration):
            itinerary.append({
                "action": "meet",
                "location": location,
                "person": person,
                "start_time": meeting_start.strftime('%H:%M'),
                "end_time": meeting_end.strftime('%H:%M')
            })
            current_time = meeting_end
            visited.add(person)

    # Prioritize meetings based on constraints
    for person, details in meetings.items():
        if person not in visited:
            visit(details['location'], person, details['start'], details['end'], details['min_duration'])

    return itinerary

itinerary = find_schedule()
result = {"itinerary": itinerary}
print(json.dumps(result))