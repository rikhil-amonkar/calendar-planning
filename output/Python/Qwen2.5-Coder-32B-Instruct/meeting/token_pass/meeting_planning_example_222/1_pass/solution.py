import json
from datetime import datetime, timedelta

# Define travel times in minutes
travel_times = {
    ('Nob Hill', 'North Beach'): 8,
    ('Nob Hill', 'Fisherman\'s Wharf'): 11,
    ('Nob Hill', 'Bayview'): 19,
    ('North Beach', 'Nob Hill'): 7,
    ('North Beach', 'Fisherman\'s Wharf'): 5,
    ('North Beach', 'Bayview'): 22,
    ('Fisherman\'s Wharf', 'Nob Hill'): 11,
    ('Fisherman\'s Wharf', 'North Beach'): 6,
    ('Fisherman\'s Wharf', 'Bayview'): 26,
    ('Bayview', 'Nob Hill'): 20,
    ('Bayview', 'North Beach'): 21,
    ('Bayview', 'Fisherman\'s Wharf'): 25
}

# Define availability and meeting constraints
availability = {
    'Helen': {'start': '7:00', 'end': '16:45', 'min_duration': 120},
    'Kimberly': {'start': '16:30', 'end': '21:00', 'min_duration': 45},
    'Patricia': {'start': '18:00', 'end': '21:15', 'min_duration': 120}
}

def time_to_minutes(time_str):
    return int(time_str[:2]) * 60 + int(time_str[3:])

def minutes_to_time(minutes):
    hours = minutes // 60
    minutes = minutes % 60
    return f"{hours}:{minutes:02}"

def get_possible_meetings(person, availability):
    start = time_to_minutes(availability['start'])
    end = time_to_minutes(availability['end'])
    min_duration = availability['min_duration']
    possible_meetings = []
    current_start = start
    while current_start + min_duration <= end:
        possible_meetings.append((current_start, current_start + min_duration))
        current_start += 15  # Increment by 15 minutes for finer granularity
    return possible_meetings

def find_optimal_schedule(start_location, start_time, availability, travel_times):
    possible_schedules = []
    current_location = start_location
    current_time = start_time
    
    def dfs(current_location, current_time, visited, schedule):
        nonlocal possible_schedules
        if len(visited) == len(availability):
            possible_schedules.append(schedule.copy())
            return
        
        for person, avail in availability.items():
            if person in visited:
                continue
            for start, end in get_possible_meetings(person, avail):
                travel_time = travel_times.get((current_location, avail['location']), float('inf'))
                if current_time + travel_time <= start:
                    new_time = end
                    if new_time <= 24 * 60:
                        schedule.append({
                            "action": "meet",
                            "location": avail['location'],
                            "person": person,
                            "start_time": minutes_to_time(start),
                            "end_time": minutes_to_time(end)
                        })
                        dfs(avail['location'], new_time, visited | {person}, schedule)
                        schedule.pop()
    
    dfs(current_location, current_time, set(), [])
    
    # Find the longest schedule
    optimal_schedule = max(possible_schedules, key=len, default=[])
    return optimal_schedule

# Set up availability with locations
availability_with_locations = {
    'Helen': {'start': '7:00', 'end': '16:45', 'min_duration': 120, 'location': 'North Beach'},
    'Kimberly': {'start': '16:30', 'end': '21:00', 'min_duration': 45, 'location': 'Fisherman\'s Wharf'},
    'Patricia': {'start': '18:00', 'end': '21:15', 'min_duration': 120, 'location': 'Bayview'}
}

# Initial conditions
start_location = 'Nob Hill'
start_time = time_to_minutes('9:00')

# Find the optimal schedule
optimal_schedule = find_optimal_schedule(start_location, start_time, availability_with_locations, travel_times)

# Format the output as JSON
output = {
    "itinerary": optimal_schedule
}

print(json.dumps(output, indent=2))