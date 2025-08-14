import itertools
import json

# Define friends and their constraints
friends = [
    {'name': 'James', 'location': 'Pacific Heights', 'start': 1200, 'end': 1320, 'duration': 120},
    {'name': 'Robert', 'location': 'Chinatown', 'start': 735, 'end': 1005, 'duration': 90},
    {'name': 'Jeffrey', 'location': 'Union Square', 'start': 570, 'end': 1050, 'duration': 120},
    {'name': 'Carol', 'location': 'Mission District', 'start': 1095, 'end': 1275, 'duration': 15},
    {'name': 'Mark', 'location': 'Golden Gate Park', 'start': 690, 'end': 1065, 'duration': 15},
    {'name': 'Sandra', 'location': 'Nob Hill', 'start': 480, 'end': 930, 'duration': 15},
]

# Define travel times between locations
travel_times = {
    ('North Beach', 'Pacific Heights'): 8,
    ('North Beach', 'Chinatown'): 6,
    ('North Beach', 'Union Square'): 7,
    ('North Beach', 'Mission District'): 18,
    ('North Beach', 'Golden Gate Park'): 22,
    ('North Beach', 'Nob Hill'): 7,
    ('Pacific Heights', 'North Beach'): 9,
    ('Pacific Heights', 'Chinatown'): 11,
    ('Pacific Heights', 'Union Square'): 12,
    ('Pacific Heights', 'Mission District'): 15,
    ('Pacific Heights', 'Golden Gate Park'): 15,
    ('Pacific Heights', 'Nob Hill'): 8,
    ('Chinatown', 'North Beach'): 3,
    ('Chinatown', 'Pacific Heights'): 10,
    ('Chinatown', 'Union Square'): 7,
    ('Chinatown', 'Mission District'): 18,
    ('Chinatown', 'Golden Gate Park'): 23,
    ('Chinatown', 'Nob Hill'): 8,
    ('Union Square', 'North Beach'): 10,
    ('Union Square', 'Pacific Heights'): 15,
    ('Union Square', 'Chinatown'): 7,
    ('Union Square', 'Mission District'): 14,
    ('Union Square', 'Golden Gate Park'): 22,
    ('Union Square', 'Nob Hill'): 9,
    ('Mission District', 'North Beach'): 17,
    ('Mission District', 'Pacific Heights'): 16,
    ('Mission District', 'Chinatown'): 16,
    ('Mission District', 'Union Square'): 15,
    ('Mission District', 'Golden Gate Park'): 17,
    ('Mission District', 'Nob Hill'): 12,
    ('Golden Gate Park', 'North Beach'): 24,
    ('Golden Gate Park', 'Pacific Heights'): 16,
    ('Golden Gate Park', 'Chinatown'): 23,
    ('Golden Gate Park', 'Union Square'): 22,
    ('Golden Gate Park', 'Mission District'): 17,
    ('Golden Gate Park', 'Nob Hill'): 20,
    ('Nob Hill', 'North Beach'): 8,
    ('Nob Hill', 'Pacific Heights'): 8,
    ('Nob Hill', 'Chinatown'): 6,
    ('Nob Hill', 'Union Square'): 7,
    ('Nob Hill', 'Mission District'): 13,
    ('Nob Hill', 'Golden Gate Park'): 17,
}

def minutes_to_time_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

def is_valid_permutation(perm):
    current_time = 540  # 9:00 AM
    current_location = 'North Beach'
    itinerary = []
    for friend in perm:
        # Calculate travel time
        from_loc = current_location
        to_loc = friend['location']
        travel_time = travel_times[(from_loc, to_loc)]
        current_time += travel_time
        # Calculate earliest start time
        earliest_start = max(current_time, friend['start'])
        # Check if meeting is possible
        if earliest_start + friend['duration'] > friend['end']:
            return None  # invalid
        # Record the meeting
        start_time_str = minutes_to_time_str(earliest_start)
        end_time_str = minutes_to_time_str(earliest_start + friend['duration'])
        itinerary.append({
            'action': 'meet',
            'location': friend['location'],
            'person': friend['name'],
            'start_time': start_time_str,
            'end_time': end_time_str
        })
        # Update current time and location
        current_time = earliest_start + friend['duration']
        current_location = to_loc
    return itinerary

best_itinerary = None
best_length = -1

# Generate all permutations of friends
for perm in itertools.permutations(friends):
    itinerary = is_valid_permutation(perm)
    if itinerary:
        if len(itinerary) > best_length:
            best_length = len(itinerary)
            best_itinerary = itinerary

# Output the result as JSON
result = {"itinerary": best_itinerary}
print(json.dumps(result, indent=2))