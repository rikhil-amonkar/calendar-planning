import json
from datetime import datetime, timedelta

# Define travel times
travel_times = {
    ('The Castro', 'Bayview'): 19,
    ('The Castro', 'Pacific Heights'): 16,
    ('The Castro', 'Alamo Square'): 8,
    ('The Castro', 'Fisherman\'s Wharf'): 24,
    ('The Castro', 'Golden Gate Park'): 11,
    ('Bayview', 'The Castro'): 20,
    ('Bayview', 'Pacific Heights'): 23,
    ('Bayview', 'Alamo Square'): 16,
    ('Bayview', 'Fisherman\'s Wharf'): 25,
    ('Bayview', 'Golden Gate Park'): 22,
    ('Pacific Heights', 'The Castro'): 16,
    ('Pacific Heights', 'Bayview'): 22,
    ('Pacific Heights', 'Alamo Square'): 10,
    ('Pacific Heights', 'Fisherman\'s Wharf'): 13,
    ('Pacific Heights', 'Golden Gate Park'): 15,
    ('Alamo Square', 'The Castro'): 8,
    ('Alamo Square', 'Bayview'): 16,
    ('Alamo Square', 'Pacific Heights'): 10,
    ('Alamo Square', 'Fisherman\'s Wharf'): 19,
    ('Alamo Square', 'Golden Gate Park'): 9,
    ('Fisherman\'s Wharf', 'The Castro'): 26,
    ('Fisherman\'s Wharf', 'Bayview'): 26,
    ('Fisherman\'s Wharf', 'Pacific Heights'): 12,
    ('Fisherman\'s Wharf', 'Alamo Square'): 20,
    ('Fisherman\'s Wharf', 'Golden Gate Park'): 25,
    ('Golden Gate Park', 'The Castro'): 13,
    ('Golden Gate Park', 'Bayview'): 23,
    ('Golden Gate Park', 'Pacific Heights'): 16,
    ('Golden Gate Park', 'Alamo Square'): 10,
    ('Golden Gate Park', 'Fisherman\'s Wharf'): 24,
}

# Define meeting constraints
constraints = {
    'Rebecca': {'location': 'Bayview', 'start': '9:00', 'end': '12:45', 'min_duration': 90},
    'Amanda': {'location': 'Pacific Heights', 'start': '18:30', 'end': '21:45', 'min_duration': 90},
    'James': {'location': 'Alamo Square', 'start': '9:45', 'end': '21:15', 'min_duration': 90},
    'Sarah': {'location': 'Fisherman\'s Wharf', 'start': '8:00', 'end': '21:30', 'min_duration': 90},
    'Melissa': {'location': 'Golden Gate Park', 'start': '9:00', 'end': '18:45', 'min_duration': 90},
}

def parse_time(time_str):
    return datetime.strptime(time_str, '%H:%M')

def add_minutes(time, minutes):
    return time + timedelta(minutes=minutes)

def can_meet(start, end, min_duration):
    return (end - start).total_seconds() / 60 >= min_duration

def find_meeting_time(constraint, current_time):
    start = max(parse_time(constraint['start']), current_time)
    end = parse_time(constraint['end'])
    if can_meet(start, end, constraint['min_duration']):
        return start, add_minutes(start, constraint['min_duration'])
    return None, None

def calculate_schedule():
    itinerary = []
    current_location = 'The Castro'
    current_time = parse_time('9:00')
    
    # Sort locations by earliest available meeting time
    sorted_constraints = sorted(constraints.items(), key=lambda x: parse_time(x[1]['start']))
    
    for name, constraint in sorted_constraints:
        location = constraint['location']
        if location != current_location:
            travel_time = travel_times[(current_location, location)]
            current_time = add_minutes(current_time, travel_time)
        
        meet_start, meet_end = find_meeting_time(constraint, current_time)
        if meet_start and meet_end:
            itinerary.append({
                'action': 'meet',
                'location': location,
                'person': name,
                'start_time': meet_start.strftime('%H:%M'),
                'end_time': meet_end.strftime('%H:%M')
            })
            current_time = meet_end
            current_location = location
    
    return itinerary

schedule = calculate_schedule()
result = {
    'itinerary': schedule
}

print(json.dumps(result))