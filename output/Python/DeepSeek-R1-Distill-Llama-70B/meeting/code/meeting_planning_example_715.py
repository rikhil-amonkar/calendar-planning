import json

# Define travel times between locations in minutes
travel_times = {
    ('Presidio', 'Marina District'): 11,
    ('Presidio', 'The Castro'): 21,
    ('Presidio', 'Fisherman\'s Wharf'): 19,
    ('Presidio', 'Bayview'): 31,
    ('Presidio', 'Pacific Heights'): 11,
    ('Presidio', 'Mission District'): 26,
    ('Presidio', 'Alamo Square'): 19,
    ('Presidio', 'Golden Gate Park'): 12,
    ('Marina District', 'Presidio'): 10,
    ('Marina District', 'The Castro'): 22,
    ('Marina District', 'Fisherman\'s Wharf'): 10,
    ('Marina District', 'Bayview'): 27,
    ('Marina District', 'Pacific Heights'): 7,
    ('Marina District', 'Mission District'): 20,
    ('Marina District', 'Alamo Square'): 15,
    ('Marina District', 'Golden Gate Park'): 18,
    ('The Castro', 'Presidio'): 20,
    ('The Castro', 'Marina District'): 21,
    ('The Castro', 'Fisherman\'s Wharf'): 24,
    ('The Castro', 'Bayview'): 19,
    ('The Castro', 'Pacific Heights'): 16,
    ('The Castro', 'Mission District'): 7,
    ('The Castro', 'Alamo Square'): 8,
    ('The Castro', 'Golden Gate Park'): 11,
    ('Fisherman\'s Wharf', 'Presidio'): 17,
    ('Fisherman\'s Wharf', 'Marina District'): 9,
    ('Fisherman\'s Wharf', 'The Castro'): 27,
    ('Fisherman\'s Wharf', 'Bayview'): 26,
    ('Fisherman\'s Wharf', 'Pacific Heights'): 12,
    ('Fisherman\'s Wharf', 'Mission District'): 22,
    ('Fisherman\'s Wharf', 'Alamo Square'): 21,
    ('Fisherman\'s Wharf', 'Golden Gate Park'): 25,
    ('Bayview', 'Presidio'): 32,
    ('Bayview', 'Marina District'): 27,
    ('Bayview', 'The Castro'): 19,
    ('Bayview', 'Fisherman\'s Wharf'): 25,
    ('Bayview', 'Pacific Heights'): 23,
    ('Bayview', 'Mission District'): 13,
    ('Bayview', 'Alamo Square'): 16,
    ('Bayview', 'Golden Gate Park'): 22,
    ('Pacific Heights', 'Presidio'): 11,
    ('Pacific Heights', 'Marina District'): 6,
    ('Pacific Heights', 'The Castro'): 16,
    ('Pacific Heights', 'Fisherman\'s Wharf'): 13,
    ('Pacific Heights', 'Bayview'): 22,
    ('Pacific Heights', 'Mission District'): 15,
    ('Pacific Heights', 'Alamo Square'): 10,
    ('Pacific Heights', 'Golden Gate Park'): 15,
    ('Mission District', 'Presidio'): 25,
    ('Mission District', 'Marina District'): 19,
    ('Mission District', 'The Castro'): 7,
    ('Mission District', 'Fisherman\'s Wharf'): 22,
    ('Mission District', 'Bayview'): 14,
    ('Mission District', 'Pacific Heights'): 16,
    ('Mission District', 'Alamo Square'): 11,
    ('Mission District', 'Golden Gate Park'): 17,
    ('Alamo Square', 'Presidio'): 17,
    ('Alamo Square', 'Marina District'): 15,
    ('Alamo Square', 'The Castro'): 8,
    ('Alamo Square', 'Fisherman\'s Wharf'): 19,
    ('Alamo Square', 'Bayview'): 16,
    ('Alamo Square', 'Pacific Heights'): 10,
    ('Alamo Square', 'Mission District'): 10,
    ('Alamo Square', 'Golden Gate Park'): 9,
    ('Golden Gate Park', 'Presidio'): 11,
    ('Golden Gate Park', 'Marina District'): 16,
    ('Golden Gate Park', 'The Castro'): 13,
    ('Golden Gate Park', 'Fisherman\'s Wharf'): 24,
    ('Golden Gate Park', 'Bayview'): 23,
    ('Golden Gate Park', 'Pacific Heights'): 16,
    ('Golden Gate Park', 'Mission District'): 17,
    ('Golden Gate Park', 'Alamo Square'): 9,
}

# Define friends with their constraints
friends = [
    {'name': 'Amanda', 'location': 'Marina District', 'start': 990, 'end': 1140, 'duration': 105},
    {'name': 'Melissa', 'location': 'The Castro', 'start': 570, 'end': 1020, 'duration': 30},
    {'name': 'Jeffrey', 'location': 'Fisherman\'s Wharf', 'start': 780, 'end': 1125, 'duration': 120},
    {'name': 'Matthew', 'location': 'Bayview', 'start': 615, 'end': 810, 'duration': 30},
    {'name': 'Nancy', 'location': 'Pacific Heights', 'start': 1020, 'end': 1410, 'duration': 105},
    {'name': 'Karen', 'location': 'Mission District', 'start': 1050, 'end': 1260, 'duration': 105},
    {'name': 'Robert', 'location': 'Alamo Square', 'start': 690, 'end': 990, 'duration': 120},
    {'name': 'Joseph', 'location': 'Golden Gate Park', 'start': 510, 'end': 1410, 'duration': 105},
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
backtrack('Presidio', start_time, set(), [])

# Prepare the output
output = {
    "itinerary": best_itinerary
}

# Print the JSON
print(json.dumps(output))