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
    
    def dfs(current_location, current_time, itinerary):
        if len(itinerary) == len(constraints):
            return itinerary
        
        for person, constraint in constraints.items():
            if person in visited:
                continue
            
            if constraint['location'] == current_location:
                start, end = find_meeting_time(constraint, current_time)
                if start and end:
                    visited.add(person)
                    itinerary.append({
                        "action": "meet",
                        "location": current_location,
                        "person": person,
                        "start_time": time_to_str(start),
                        "end_time": time_to_str(end)
                    })
                    return dfs(current_location, end, itinerary)
        
        next_locations = sorted([(travel_times[(current_location, loc)], loc) for loc in locations if loc != current_location and loc not in [c['location'] for c in constraints.values() if c['location'] in visited]])
        
        for travel_time, next_location in next_locations:
            next_arrival = add_minutes(current_time, travel_time)
            for person, constraint in constraints.items():
                if person in visited:
                    continue
                
                if constraint['location'] == next_location:
                    start, end = find_meeting_time(constraint, next_arrival)
                    if start and end:
                        visited.add(person)
                        itinerary.append({
                            "action": "travel",
                            "location": next_location,
                            "person": None,
                            "start_time": time_to_str(current_time),
                            "end_time": time_to_str(next_arrival)
                        })
                        itinerary.append({
                            "action": "meet",
                            "location": next_location,
                            "person": person,
                            "start_time": time_to_str(start),
                            "end_time": time_to_str(end)
                        })
                        return dfs(next_location, end, itinerary)
        
        return None
    
    final_itinerary = dfs('Nob Hill', current_time, itinerary)
    return final_itinerary

schedule = calculate_schedule()
print(json.dumps({"itinerary": schedule}, indent=2))