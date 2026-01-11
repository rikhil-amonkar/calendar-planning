import json

# Constants
START_TIME = 9 * 60  # 9:00 AM in minutes
END_TIME = 24 * 60   # 24:00 (midnight) in minutes

# Travel times in minutes
travel_times = {
    ('Sunset District', 'Alamo Square'): 17,
    ('Sunset District', 'Russian Hill'): 24,
    ('Sunset District', 'Golden Gate Park'): 11,
    ('Sunset District', 'Mission District'): 24,
    ('Alamo Square', 'Sunset District'): 16,
    ('Alamo Square', 'Russian Hill'): 13,
    ('Alamo Square', 'Golden Gate Park'): 9,
    ('Alamo Square', 'Mission District'): 10,
    ('Russian Hill', 'Sunset District'): 23,
    ('Russian Hill', 'Alamo Square'): 15,
    ('Russian Hill', 'Golden Gate Park'): 21,
    ('Russian Hill', 'Mission District'): 16,
    ('Golden Gate Park', 'Sunset District'): 10,
    ('Golden Gate Park', 'Alamo Square'): 10,
    ('Golden Gate Park', 'Russian Hill'): 19,
    ('Golden Gate Park', 'Mission District'): 17,
    ('Mission District', 'Sunset District'): 24,
    ('Mission District', 'Alamo Square'): 11,
    ('Mission District', 'Russian Hill'): 15,
    ('Mission District', 'Golden Gate Park'): 17,
}

# Meeting constraints
meetings = {
    'Charles': {'location': 'Alamo Square', 'start': 18 * 60, 'end': 20 * 60 + 45, 'min_duration': 90},
    'Margaret': {'location': 'Russian Hill', 'start': 9 * 60, 'end': 16 * 60, 'min_duration': 30},
    'Daniel': {'location': 'Golden Gate Park', 'start': 8 * 60, 'end': 1 * 60 + 30, 'min_duration': 15},
    'Stephanie': {'location': 'Mission District', 'start': 20 * 60 + 30, 'end': 22 * 60, 'min_duration': 90},
}

# Convert times to HH:MM format
def time_to_str(minutes):
    hours, mins = divmod(minutes, 60)
    return f"{hours}:{mins:02}"

# Recursive function to find the best schedule
def find_schedule(current_location, current_time, visited, itinerary):
    global best_itinerary
    global best_duration
    
    # Check if all meetings are visited
    if len(visited) == len(meetings):
        total_duration = sum((meeting['end'] - meeting['start']) for meeting in itinerary)
        if total_duration > best_duration:
            best_duration = total_duration
            best_itinerary = itinerary[:]
        return
    
    # Try to visit each friend
    for person, meeting in meetings.items():
        if person not in visited:
            location = meeting['location']
            travel_time = travel_times[(current_location, location)]
            meet_start = max(current_time + travel_time, meeting['start'])
            meet_end = meet_start + meeting['min_duration']
            
            if meet_end <= meeting['end']:
                new_itinerary = itinerary + [{
                    'action': 'meet',
                    'location': location,
                    'person': person,
                    'start_time': time_to_str(meet_start),
                    'end_time': time_to_str(meet_end)
                }]
                find_schedule(location, meet_end, visited | {person}, new_itinerary)

# Initialize best itinerary and duration
best_itinerary = []
best_duration = 0

# Start the search from Sunset District
find_schedule('Sunset District', START_TIME, set(), [])

# Output the best itinerary in JSON format
output = {
    "itinerary": best_itinerary
}

print(json.dumps(output, indent=2))