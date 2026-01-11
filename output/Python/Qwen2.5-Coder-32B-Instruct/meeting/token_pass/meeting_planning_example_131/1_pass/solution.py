import json
from datetime import datetime, timedelta

# Define travel times
travel_times = {
    ('Pacific Heights', 'Presidio'): 11,
    ('Pacific Heights', 'Marina District'): 6,
    ('Presidio', 'Pacific Heights'): 11,
    ('Presidio', 'Marina District'): 10,
    ('Marina District', 'Pacific Heights'): 7,
    ('Marina District', 'Presidio'): 10,
}

# Define constraints
constraints = {
    'Jason': {'location': 'Presidio', 'start': '10:00', 'end': '16:15', 'min_duration': 90},
    'Kenneth': {'location': 'Marina District', 'start': '15:30', 'end': '16:45', 'min_duration': 45},
}

# Start time
start_time = datetime.strptime('9:00', '%H:%M')

def parse_time(time_str):
    return datetime.strptime(time_str, '%H:%M')

def add_minutes(time, minutes):
    return time + timedelta(minutes=minutes)

def can_meet(start_time, end_time, min_duration):
    return (end_time - start_time).total_seconds() / 60 >= min_duration

def get_meeting_schedule():
    itinerary = []
    current_time = start_time
    current_location = 'Pacific Heights'
    
    # Try to meet Jason first
    jason_start = parse_time(constraints['Jason']['start'])
    jason_end = parse_time(constraints['Jason']['end'])
    jason_min_duration = constraints['Jason']['min_duration']
    
    # Travel to Presidio
    travel_to_presidio = travel_times[(current_location, 'Presidio')]
    arrival_time_at_presidio = add_minutes(current_time, travel_to_presidio)
    
    # Check if we can meet Jason
    if arrival_time_at_presidio <= jason_end:
        meeting_start = max(arrival_time_at_presidio, jason_start)
        meeting_end = min(add_minutes(meeting_start, jason_min_duration), jason_end)
        
        if can_meet(meeting_start, meeting_end, jason_min_duration):
            itinerary.append({
                "action": "meet",
                "location": "Presidio",
                "person": "Jason",
                "start_time": meeting_start.strftime('%H:%M'),
                "end_time": meeting_end.strftime('%H:%M')
            })
            current_time = meeting_end
            current_location = 'Presidio'
    
    # Try to meet Kenneth next
    kenneth_start = parse_time(constraints['Kenneth']['start'])
    kenneth_end = parse_time(constraints['Kenneth']['end'])
    kenneth_min_duration = constraints['Kenneth']['min_duration']
    
    # Travel to Marina District
    travel_to_marina = travel_times[(current_location, 'Marina District')]
    arrival_time_at_marina = add_minutes(current_time, travel_to_marina)
    
    # Check if we can meet Kenneth
    if arrival_time_at_marina <= kenneth_end:
        meeting_start = max(arrival_time_at_marina, kenneth_start)
        meeting_end = min(add_minutes(meeting_start, kenneth_min_duration), kenneth_end)
        
        if can_meet(meeting_start, meeting_end, kenneth_min_duration):
            itinerary.append({
                "action": "meet",
                "location": "Marina District",
                "person": "Kenneth",
                "start_time": meeting_start.strftime('%H:%M'),
                "end_time": meeting_end.strftime('%H:%M')
            })
    
    return itinerary

# Generate the schedule
schedule = {
    "itinerary": get_meeting_schedule()
}

# Output the schedule as JSON
print(json.dumps(schedule, indent=2))