import json

# Define travel times between locations in minutes
travel_times = {
    ('Haight-Ashbury', 'Russian Hill'): 17,
    ('Haight-Ashbury', 'Fisherman\'s Wharf'): 23,
    ('Haight-Ashbury', 'Nob Hill'): 15,
    ('Haight-Ashbury', 'Golden Gate Park'): 7,
    ('Haight-Ashbury', 'Alamo Square'): 5,
    ('Haight-Ashbury', 'Pacific Heights'): 12,
    ('Russian Hill', 'Haight-Ashbury'): 17,
    ('Russian Hill', 'Fisherman\'s Wharf'): 7,
    ('Russian Hill', 'Nob Hill'): 5,
    ('Russian Hill', 'Golden Gate Park'): 21,
    ('Russian Hill', 'Alamo Square'): 15,
    ('Russian Hill', 'Pacific Heights'): 7,
    ('Fisherman\'s Wharf', 'Haight-Ashbury'): 22,
    ('Fisherman\'s Wharf', 'Russian Hill'): 7,
    ('Fisherman\'s Wharf', 'Nob Hill'): 11,
    ('Fisherman\'s Wharf', 'Golden Gate Park'): 25,
    ('Fisherman\'s Wharf', 'Alamo Square'): 20,
    ('Fisherman\'s Wharf', 'Pacific Heights'): 12,
    ('Nob Hill', 'Haight-Ashbury'): 13,
    ('Nob Hill', 'Russian Hill'): 5,
    ('Nob Hill', 'Fisherman\'s Wharf'): 11,
    ('Nob Hill', 'Golden Gate Park'): 17,
    ('Nob Hill', 'Alamo Square'): 11,
    ('Nob Hill', 'Pacific Heights'): 8,
    ('Golden Gate Park', 'Haight-Ashbury'): 7,
    ('Golden Gate Park', 'Russian Hill'): 19,
    ('Golden Gate Park', 'Fisherman\'s Wharf'): 24,
    ('Golden Gate Park', 'Nob Hill'): 20,
    ('Golden Gate Park', 'Alamo Square'): 10,
    ('Golden Gate Park', 'Pacific Heights'): 16,
    ('Alamo Square', 'Haight-Ashbury'): 5,
    ('Alamo Square', 'Russian Hill'): 13,
    ('Alamo Square', 'Fisherman\'s Wharf'): 19,
    ('Alamo Square', 'Nob Hill'): 11,
    ('Alamo Square', 'Golden Gate Park'): 9,
    ('Alamo Square', 'Pacific Heights'): 10,
    ('Pacific Heights', 'Haight-Ashbury'): 11,
    ('Pacific Heights', 'Russian Hill'): 7,
    ('Pacific Heights', 'Fisherman\'s Wharf'): 13,
    ('Pacific Heights', 'Nob Hill'): 8,
    ('Pacific Heights', 'Golden Gate Park'): 15,
    ('Pacific Heights', 'Alamo Square'): 10,
}

# Define friends with their constraints
friends = [
    {'name': 'Stephanie', 'location': 'Russian Hill', 'start': 960, 'end': 990, 'duration': 15},
    {'name': 'Kevin', 'location': 'Fisherman\'s Wharf', 'start': 1050, 'end': 1410, 'duration': 75},
    {'name': 'Robert', 'location': 'Nob Hill', 'start': 465, 'end': 630, 'duration': 90},
    {'name': 'Steven', 'location': 'Golden Gate Park', 'start': 510, 'end': 1020, 'duration': 75},
    {'name': 'Anthony', 'location': 'Alamo Square', 'start': 465, 'end': 1125, 'duration': 15},
    {'name': 'Sandra', 'location': 'Pacific Heights', 'start': 990, 'end': 1410, 'duration': 45},
]

def convert_minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

def convert_time_to_minutes(time_str):
    hours, mins = map(int, time_str.split(':'))
    return hours * 60 + mins

best_itinerary = []
best_count = 0

def backtrack(current_location, current_time, met, itinerary):
    global best_itinerary, best_count

    # Prune if no better solution possible
    remaining = len(friends) - len(met)
    if len(met) + remaining <= best_count:
        return

    # Update best if current is better
    if len(met) > best_count:
        best_count = len(met)
        best_itinerary = itinerary.copy()

    # Try each possible next friend
    for friend in friends:
        if friend['name'] in met:
            continue

        # Calculate travel time to friend's location
        travel = travel_times.get((current_location, friend['location']), 0)
        arrival = current_time + travel

        # Friend's availability
        start = friend['start']
        end = friend['end']
        duration = friend['duration']

        earliest_start = max(arrival, start)
        latest_start = end - duration

        if earliest_start > latest_start:
            continue  # Cannot meet this friend

        # Schedule the meeting
        meeting_start = earliest_start
        meeting_end = meeting_start + duration

        # Create meeting entry
        meeting = {
            'action': 'meet',
            'location': friend['location'],
            'person': friend['name'],
            'start_time': convert_minutes_to_time(meeting_start),
            'end_time': convert_minutes_to_time(meeting_end)
        }

        # Update the state
        new_met = set(met)
        new_met.add(friend['name'])
        new_itinerary = itinerary.copy()
        new_itinerary.append(meeting)

        # Update current location and time
        new_location = friend['location']
        new_time = meeting_end

        # Recurse
        backtrack(new_location, new_time, new_met, new_itinerary)

# Initial call
start_time = 540  # 9:00 AM in minutes
backtrack('Haight-Ashbury', start_time, set(), [])

# Prepare the output
output = {
    "itinerary": best_itinerary
}

# Print the JSON
print(json.dumps(output))