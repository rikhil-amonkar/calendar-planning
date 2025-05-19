import json

# Define travel times between locations in minutes
travel_times = {
    ('Haight-Ashbury', 'Mission District'): 11,
    ('Haight-Ashbury', 'Union Square'): 19,
    ('Haight-Ashbury', 'Pacific Heights'): 12,
    ('Haight-Ashbury', 'Bayview'): 18,
    ('Haight-Ashbury', 'Fisherman\'s Wharf'): 23,
    ('Haight-Ashbury', 'Marina District'): 17,
    ('Haight-Ashbury', 'Richmond District'): 10,
    ('Haight-Ashbury', 'Sunset District'): 15,
    ('Haight-Ashbury', 'Golden Gate Park'): 7,
    ('Mission District', 'Haight-Ashbury'): 12,
    ('Mission District', 'Union Square'): 15,
    ('Mission District', 'Pacific Heights'): 16,
    ('Mission District', 'Bayview'): 14,
    ('Mission District', 'Fisherman\'s Wharf'): 22,
    ('Mission District', 'Marina District'): 19,
    ('Mission District', 'Richmond District'): 20,
    ('Mission District', 'Sunset District'): 24,
    ('Mission District', 'Golden Gate Park'): 17,
    ('Union Square', 'Haight-Ashbury'): 18,
    ('Union Square', 'Mission District'): 14,
    ('Union Square', 'Pacific Heights'): 15,
    ('Union Square', 'Bayview'): 15,
    ('Union Square', 'Fisherman\'s Wharf'): 15,
    ('Union Square', 'Marina District'): 18,
    ('Union Square', 'Richmond District'): 20,
    ('Union Square', 'Sunset District'): 27,
    ('Union Square', 'Golden Gate Park'): 22,
    ('Pacific Heights', 'Haight-Ashbury'): 11,
    ('Pacific Heights', 'Mission District'): 15,
    ('Pacific Heights', 'Union Square'): 12,
    ('Pacific Heights', 'Bayview'): 22,
    ('Pacific Heights', 'Fisherman\'s Wharf'): 13,
    ('Pacific Heights', 'Marina District'): 6,
    ('Pacific Heights', 'Richmond District'): 12,
    ('Pacific Heights', 'Sunset District'): 21,
    ('Pacific Heights', 'Golden Gate Park'): 15,
    ('Bayview', 'Haight-Ashbury'): 19,
    ('Bayview', 'Mission District'): 13,
    ('Bayview', 'Union Square'): 18,
    ('Bayview', 'Pacific Heights'): 23,
    ('Bayview', 'Fisherman\'s Wharf'): 25,
    ('Bayview', 'Marina District'): 27,
    ('Bayview', 'Richmond District'): 25,
    ('Bayview', 'Sunset District'): 23,
    ('Bayview', 'Golden Gate Park'): 22,
    ('Fisherman\'s Wharf', 'Haight-Ashbury'): 22,
    ('Fisherman\'s Wharf', 'Mission District'): 22,
    ('Fisherman\'s Wharf', 'Union Square'): 13,
    ('Fisherman\'s Wharf', 'Pacific Heights'): 12,
    ('Fisherman\'s Wharf', 'Bayview'): 26,
    ('Fisherman\'s Wharf', 'Marina District'): 9,
    ('Fisherman\'s Wharf', 'Richmond District'): 18,
    ('Fisherman\'s Wharf', 'Sunset District'): 27,
    ('Fisherman\'s Wharf', 'Golden Gate Park'): 25,
    ('Marina District', 'Haight-Ashbury'): 16,
    ('Marina District', 'Mission District'): 20,
    ('Marina District', 'Union Square'): 16,
    ('Marina District', 'Pacific Heights'): 7,
    ('Marina District', 'Bayview'): 27,
    ('Marina District', 'Fisherman\'s Wharf'): 10,
    ('Marina District', 'Richmond District'): 11,
    ('Marina District', 'Sunset District'): 19,
    ('Marina District', 'Golden Gate Park'): 18,
    ('Richmond District', 'Haight-Ashbury'): 10,
    ('Richmond District', 'Mission District'): 20,
    ('Richmond District', 'Union Square'): 21,
    ('Richmond District', 'Pacific Heights'): 10,
    ('Richmond District', 'Bayview'): 27,
    ('Richmond District', 'Fisherman\'s Wharf'): 18,
    ('Richmond District', 'Marina District'): 9,
    ('Richmond District', 'Sunset District'): 11,
    ('Richmond District', 'Golden Gate Park'): 9,
    ('Sunset District', 'Haight-Ashbury'): 15,
    ('Sunset District', 'Mission District'): 25,
    ('Sunset District', 'Union Square'): 30,
    ('Sunset District', 'Pacific Heights'): 21,
    ('Sunset District', 'Bayview'): 22,
    ('Sunset District', 'Fisherman\'s Wharf'): 29,
    ('Sunset District', 'Marina District'): 21,
    ('Sunset District', 'Richmond District'): 12,
    ('Sunset District', 'Golden Gate Park'): 11,
    ('Golden Gate Park', 'Haight-Ashbury'): 7,
    ('Golden Gate Park', 'Mission District'): 17,
    ('Golden Gate Park', 'Union Square'): 22,
    ('Golden Gate Park', 'Pacific Heights'): 16,
    ('Golden Gate Park', 'Bayview'): 23,
    ('Golden Gate Park', 'Fisherman\'s Wharf'): 24,
    ('Golden Gate Park', 'Marina District'): 16,
    ('Golden Gate Park', 'Richmond District'): 7,
    ('Golden Gate Park', 'Sunset District'): 10,
}

# Define friends with their constraints
friends = [
    {'name': 'Elizabeth', 'location': 'Mission District', 'start': 630, 'end': 1200, 'duration': 90},
    {'name': 'David', 'location': 'Union Square', 'start': 915, 'end': 1050, 'duration': 45},
    {'name': 'Sandra', 'location': 'Pacific Heights', 'start': 420, 'end': 1200, 'duration': 120},
    {'name': 'Thomas', 'location': 'Bayview', 'start': 1170, 'end': 1260, 'duration': 30},
    {'name': 'Robert', 'location': 'Fisherman\'s Wharf', 'start': 600, 'end': 900, 'duration': 15},
    {'name': 'Kenneth', 'location': 'Marina District', 'start': 645, 'end': 780, 'duration': 45},
    {'name': 'Melissa', 'location': 'Richmond District', 'start': 1035, 'end': 1200, 'duration': 15},
    {'name': 'Kimberly', 'location': 'Sunset District', 'start': 615, 'end': 1085, 'duration': 105},
    {'name': 'Amanda', 'location': 'Golden Gate Park', 'start': 465, 'end': 1170, 'duration': 15},
]

def convert_minutes(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

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
        travel = travel_times[(current_location, friend['location'])]
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
            'start_time': convert_minutes(meeting_start),
            'end_time': convert_minutes(meeting_end)
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
backtrack('Haight-Ashbury', 540, set(), [])

# Prepare the output
output = {
    "itinerary": best_itinerary
}

# Print the JSON
print(json.dumps(output))