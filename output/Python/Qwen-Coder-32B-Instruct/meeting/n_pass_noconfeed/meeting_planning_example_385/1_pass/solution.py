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
meetings = {
    'Jeffrey': {'location': 'Presidio', 'start': '8:00', 'end': '10:00', 'min_duration': 105},
    'Steven': {'location': 'North Beach', 'start': '13:30', 'end': '22:00', 'min_duration': 45},
    'Barbara': {'location': 'Fisherman\'s Wharf', 'start': '18:00', 'end': '21:30', 'min_duration': 30},
    'John': {'location': 'Pacific Heights', 'start': '9:00', 'end': '13:30', 'min_duration': 15}
}

def parse_time(time_str):
    return datetime.strptime(time_str, '%H:%M')

def format_time(dt):
    return dt.strftime('%H:%M')

def find_meeting_time(person, current_time):
    start = parse_time(meetings[person]['start'])
    end = parse_time(meetings[person]['end'])
    min_duration = meetings[person]['min_duration']
    
    if current_time >= end:
        return None
    
    if current_time < start:
        current_time = start
    
    meeting_end = current_time + timedelta(minutes=min_duration)
    
    if meeting_end <= end:
        return current_time, meeting_end
    else:
        return None

def calculate_schedule():
    itinerary = []
    current_location = 'Nob Hill'
    current_time = parse_time('9:00')
    
    for person in ['Jeffrey', 'John', 'Steven', 'Barbara']:
        location = meetings[person]['location']
        
        # Calculate travel time
        travel_time = travel_times[(current_location, location)]
        arrival_time = current_time + timedelta(minutes=travel_time)
        
        # Find meeting time
        meeting_time = find_meeting_time(person, arrival_time)
        if meeting_time:
            start_time, end_time = meeting_time
            itinerary.append({
                "action": "meet",
                "location": location,
                "person": person,
                "start_time": format_time(start_time),
                "end_time": format_time(end_time)
            })
            current_time = end_time
            current_location = location
        else:
            continue
    
    return itinerary

schedule = calculate_schedule()
print(json.dumps({"itinerary": schedule}))