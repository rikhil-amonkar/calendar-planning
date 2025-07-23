import json
from datetime import datetime, timedelta

# Define travel times
travel_times = {
    ('Bayview', 'Russian Hill'): 23,
    ('Bayview', 'Alamo Square'): 16,
    ('Bayview', 'North Beach'): 21,
    ('Bayview', 'Financial District'): 19,
    ('Russian Hill', 'Bayview'): 23,
    ('Russian Hill', 'Alamo Square'): 15,
    ('Russian Hill', 'North Beach'): 5,
    ('Russian Hill', 'Financial District'): 11,
    ('Alamo Square', 'Bayview'): 16,
    ('Alamo Square', 'Russian Hill'): 13,
    ('Alamo Square', 'North Beach'): 15,
    ('Alamo Square', 'Financial District'): 17,
    ('North Beach', 'Bayview'): 22,
    ('North Beach', 'Russian Hill'): 4,
    ('North Beach', 'Alamo Square'): 16,
    ('North Beach', 'Financial District'): 8,
    ('Financial District', 'Bayview'): 19,
    ('Financial District', 'Russian Hill'): 10,
    ('Financial District', 'Alamo Square'): 17,
    ('Financial District', 'North Beach'): 7,
}

# Define constraints
constraints = {
    'Joseph': {'location': 'Russian Hill', 'start': '8:30', 'end': '19:15', 'min_duration': 60},
    'Nancy': {'location': 'Alamo Square', 'start': '11:00', 'end': '16:00', 'min_duration': 90},
    'Jason': {'location': 'North Beach', 'start': '16:45', 'end': '21:45', 'min_duration': 15},
    'Jeffrey': {'location': 'Financial District', 'start': '10:30', 'end': '15:45', 'min_duration': 45},
}

def parse_time(time_str):
    return datetime.strptime(time_str, '%H:%M')

def time_to_str(time_obj):
    return time_obj.strftime('%H:%M')

def find_meeting_slot(person, current_time):
    start = parse_time(constraints[person]['start'])
    end = parse_time(constraints[person]['end'])
    min_duration = constraints[person]['min_duration']
    
    while start < end:
        slot_end = start + timedelta(minutes=min_duration)
        if slot_end <= end and start >= current_time:
            return start, slot_end
        start += timedelta(minutes=1)
    return None, None

def calculate_itinerary():
    current_location = 'Bayview'
    current_time = parse_time('9:00')
    itinerary = []

    # Priority order: Joseph, Nancy, Jeffrey, Jason
    priority_order = ['Joseph', 'Nancy', 'Jeffrey', 'Jason']
    visited = set()

    while len(visited) < len(priority_order):
        next_person = None
        next_start = None
        next_end = None
        next_travel_time = float('inf')
        
        for person in priority_order:
            if person in visited:
                continue
            
            location = constraints[person]['location']
            start, end = find_meeting_slot(person, current_time)
            
            if start is None:
                continue
            
            travel_time = travel_times[(current_location, location)]
            if start >= current_time + timedelta(minutes=travel_time) and travel_time < next_travel_time:
                next_person = person
                next_start = start
                next_end = end
                next_travel_time = travel_time
        
        if next_person is None:
            break
        
        # Travel to the next location
        travel_time = travel_times[(current_location, constraints[next_person]['location'])]
        current_time += timedelta(minutes=travel_time)
        current_location = constraints[next_person]['location']
        
        # Meet the person
        itinerary.append({
            "action": "meet",
            "location": constraints[next_person]['location'],
            "person": next_person,
            "start_time": time_to_str(current_time),
            "end_time": time_to_str(next_end)
        })
        
        current_time = next_end
        visited.add(next_person)

    return itinerary

itinerary = calculate_itinerary()
result = {"itinerary": itinerary}
print(json.dumps(result))