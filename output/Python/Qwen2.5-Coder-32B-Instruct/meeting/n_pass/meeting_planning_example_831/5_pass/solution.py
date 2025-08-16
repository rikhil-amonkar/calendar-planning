import json
from datetime import datetime, timedelta

# Define the travel times
travel_times = {
    ('Presidio', 'Fisherman\'s Wharf'): 19,
    ('Presidio', 'Alamo Square'): 19,
    ('Presidio', 'Financial District'): 23,
    ('Presidio', 'Union Square'): 22,
    ('Presidio', 'Sunset District'): 15,
    ('Presidio', 'Embarcadero'): 20,
    ('Presidio', 'Golden Gate Park'): 12,
    ('Presidio', 'Chinatown'): 21,
    ('Presidio', 'Richmond District'): 7,
    ('Fisherman\'s Wharf', 'Presidio'): 17,
    ('Fisherman\'s Wharf', 'Alamo Square'): 21,
    ('Fisherman\'s Wharf', 'Financial District'): 11,
    ('Fisherman\'s Wharf', 'Union Square'): 13,
    ('Fisherman\'s Wharf', 'Sunset District'): 27,
    ('Fisherman\'s Wharf', 'Embarcadero'): 8,
    ('Fisherman\'s Wharf', 'Golden Gate Park'): 25,
    ('Fisherman\'s Wharf', 'Chinatown'): 12,
    ('Fisherman\'s Wharf', 'Richmond District'): 18,
    ('Alamo Square', 'Presidio'): 17,
    ('Alamo Square', 'Fisherman\'s Wharf'): 19,
    ('Alamo Square', 'Financial District'): 17,
    ('Alamo Square', 'Union Square'): 14,
    ('Alamo Square', 'Sunset District'): 16,
    ('Alamo Square', 'Embarcadero'): 16,
    ('Alamo Square', 'Golden Gate Park'): 9,
    ('Alamo Square', 'Chinatown'): 15,
    ('Alamo Square', 'Richmond District'): 11,
    ('Financial District', 'Presidio'): 22,
    ('Financial District', 'Fisherman\'s Wharf'): 10,
    ('Financial District', 'Alamo Square'): 17,
    ('Financial District', 'Union Square'): 9,
    ('Financial District', 'Sunset District'): 30,
    ('Financial District', 'Embarcadero'): 4,
    ('Financial District', 'Golden Gate Park'): 23,
    ('Financial District', 'Chinatown'): 5,
    ('Financial District', 'Richmond District'): 21,
    ('Union Square', 'Presidio'): 24,
    ('Union Square', 'Fisherman\'s Wharf'): 15,
    ('Union Square', 'Alamo Square'): 15,
    ('Union Square', 'Financial District'): 9,
    ('Union Square', 'Sunset District'): 27,
    ('Union Square', 'Embarcadero'): 11,
    ('Union Square', 'Golden Gate Park'): 22,
    ('Union Square', 'Chinatown'): 7,
    ('Union Square', 'Richmond District'): 20,
    ('Sunset District', 'Presidio'): 16,
    ('Sunset District', 'Fisherman\'s Wharf'): 29,
    ('Sunset District', 'Alamo Square'): 17,
    ('Sunset District', 'Financial District'): 30,
    ('Sunset District', 'Union Square'): 30,
    ('Sunset District', 'Embarcadero'): 30,
    ('Sunset District', 'Golden Gate Park'): 11,
    ('Sunset District', 'Chinatown'): 29,
    ('Sunset District', 'Richmond District'): 12,
    ('Embarcadero', 'Presidio'): 20,
    ('Embarcadero', 'Fisherman\'s Wharf'): 6,
    ('Embarcadero', 'Alamo Square'): 19,
    ('Embarcadero', 'Financial District'): 5,
    ('Embarcadero', 'Union Square'): 10,
    ('Embarcadero', 'Sunset District'): 30,
    ('Embarcadero', 'Golden Gate Park'): 25,
    ('Embarcadero', 'Chinatown'): 7,
    ('Embarcadero', 'Richmond District'): 21,
    ('Golden Gate Park', 'Presidio'): 11,
    ('Golden Gate Park', 'Fisherman\'s Wharf'): 24,
    ('Golden Gate Park', 'Alamo Square'): 9,
    ('Golden Gate Park', 'Financial District'): 26,
    ('Golden Gate Park', 'Union Square'): 22,
    ('Golden Gate Park', 'Sunset District'): 10,
    ('Golden Gate Park', 'Embarcadero'): 25,
    ('Golden Gate Park', 'Chinatown'): 23,
    ('Golden Gate Park', 'Richmond District'): 7,
    ('Chinatown', 'Presidio'): 19,
    ('Chinatown', 'Fisherman\'s Wharf'): 8,
    ('Chinatown', 'Alamo Square'): 17,
    ('Chinatown', 'Financial District'): 5,
    ('Chinatown', 'Union Square'): 7,
    ('Chinatown', 'Sunset District'): 29,
    ('Chinatown', 'Embarcadero'): 5,
    ('Chinatown', 'Golden Gate Park'): 23,
    ('Chinatown', 'Richmond District'): 20,
    ('Richmond District', 'Presidio'): 7,
    ('Richmond District', 'Fisherman\'s Wharf'): 18,
    ('Richmond District', 'Alamo Square'): 13,
    ('Richmond District', 'Financial District'): 22,
    ('Richmond District', 'Union Square'): 21,
    ('Richmond District', 'Sunset District'): 11,
    ('Richmond District', 'Embarcadero'): 19,
    ('Richmond District', 'Golden Gate Park'): 9,
    ('Richmond District', 'Chinatown'): 20,
}

# Define the meeting constraints
meetings = {
    'Jeffrey': {'location': 'Fisherman\'s Wharf', 'start': '10:15', 'end': '13:00', 'min_duration': 90},
    'Ronald': {'location': 'Alamo Square', 'start': '7:45', 'end': '14:45', 'min_duration': 120},
    'Jason': {'location': 'Financial District', 'start': '10:45', 'end': '16:00', 'min_duration': 105},
    'Melissa': {'location': 'Union Square', 'start': '17:45', 'end': '18:15', 'min_duration': 15},
    'Elizabeth': {'location': 'Sunset District', 'start': '14:45', 'end': '17:30', 'min_duration': 105},
    'Margaret': {'location': 'Embarcadero', 'start': '13:15', 'end': '19:00', 'min_duration': 90},
    'George': {'location': 'Golden Gate Park', 'start': '19:00', 'end': '22:00', 'min_duration': 75},
    'Richard': {'location': 'Chinatown', 'start': '9:30', 'end': '21:00', 'min_duration': 15},
    'Laura': {'location': 'Richmond District', 'start': '9:45', 'end': '18:00', 'min_duration': 60},
}

# Convert time strings to datetime objects
def parse_time(time_str):
    return datetime.strptime(time_str, '%H:%M').time()

# Check if two time intervals overlap and return the overlap duration
def overlap(start1, end1, start2, end2):
    latest_start = max(start1, start2)
    earliest_end = min(end1, end2)
    delta = (datetime.combine(datetime.today(), earliest_end) - datetime.combine(datetime.today(), latest_start)).seconds / 60
    return delta if delta > 0 else 0

# Find the best meeting time within the available window
def find_best_meeting_time(person, current_time):
    start = parse_time(meetings[person]['start'])
    end = parse_time(meetings[person]['end'])
    min_duration = meetings[person]['min_duration']
    
    # Ensure current_time is at least the meeting start time
    if current_time < start:
        current_time = start
    
    # Find the first possible meeting time within the available window
    while current_time + timedelta(minutes=min_duration) <= end:
        test_end = current_time + timedelta(minutes=min_duration)
        if overlap(current_time, test_end, start, end) >= min_duration:
            return current_time, test_end
        current_time += timedelta(minutes=1)
    
    return None, None

# Calculate the optimal schedule
def calculate_schedule():
    current_time = parse_time('9:00')
    itinerary = []
    locations_visited = set()
    
    # Sort meetings by their start time to prioritize earlier meetings
    sorted_meetings = sorted(meetings.items(), key=lambda x: parse_time(x[1]['start']))
    
    for person, details in sorted_meetings:
        location = details['location']
        if location in locations_visited:
            continue
        
        # Find the best meeting time for the current person
        best_start, best_end = find_best_meeting_time(person, current_time)
        
        if best_start and best_end:
            # Calculate travel time to the next location
            if itinerary:
                last_location = itinerary[-1]['location']
                travel_time = travel_times[(last_location, location)]
                current_time = datetime.combine(datetime.today(), best_start) - timedelta(minutes=travel_time)
            
            # Ensure we start the meeting after traveling
            if current_time.time() < best_start:
                current_time = datetime.combine(datetime.today(), best_start)
            
            # Add the meeting to the itinerary
            itinerary.append({
                'action': 'meet',
                'location': location,
                'person': person,
                'start_time': best_start.strftime('%H:%M'),
                'end_time': best_end.strftime('%H:%M')
            })
            current_time = best_end
            locations_visited.add(location)
    
    return itinerary

# Generate the JSON output
schedule = calculate_schedule()
output = {
    'itinerary': schedule
}

print(json.dumps(output, indent=4))