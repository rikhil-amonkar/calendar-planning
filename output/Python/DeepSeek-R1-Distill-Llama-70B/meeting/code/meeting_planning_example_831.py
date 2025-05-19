import json

# Define travel times between locations in minutes
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
    ('Sunset District', 'Chinatown'): 30,
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

# Define friends with their constraints
friends = [
    {'name': 'Jeffrey', 'location': 'Fisherman\'s Wharf', 'start': 615, 'end': 780, 'duration': 90},
    {'name': 'Ronald', 'location': 'Alamo Square', 'start': 465, 'end': 930, 'duration': 120},
    {'name': 'Jason', 'location': 'Financial District', 'start': 645, 'end': 1020, 'duration': 105},
    {'name': 'Melissa', 'location': 'Union Square', 'start': 1125, 'end': 1140, 'duration': 15},
    {'name': 'Elizabeth', 'location': 'Sunset District', 'start': 990, 'end': 1215, 'duration': 105},
    {'name': 'Margaret', 'location': 'Embarcadero', 'start': 810, 'end': 1140, 'duration': 90},
    {'name': 'George', 'location': 'Golden Gate Park', 'start': 1140, 'end': 1320, 'duration': 75},
    {'name': 'Richard', 'location': 'Chinatown', 'start': 570, 'end': 1440, 'duration': 15},
    {'name': 'Laura', 'location': 'Richmond District', 'start': 585, 'end': 1080, 'duration': 60},
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