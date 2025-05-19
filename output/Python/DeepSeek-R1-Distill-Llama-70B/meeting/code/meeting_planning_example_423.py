import json

# Define travel times between locations in minutes
travel_times = {
    ('Presidio', 'Richmond District'): 7,
    ('Presidio', 'North Beach'): 18,
    ('Presidio', 'Financial District'): 23,
    ('Presidio', 'Golden Gate Park'): 12,
    ('Presidio', 'Union Square'): 22,
    ('Richmond District', 'Presidio'): 7,
    ('Richmond District', 'North Beach'): 17,
    ('Richmond District', 'Financial District'): 22,
    ('Richmond District', 'Golden Gate Park'): 9,
    ('Richmond District', 'Union Square'): 21,
    ('North Beach', 'Presidio'): 17,
    ('North Beach', 'Richmond District'): 18,
    ('North Beach', 'Financial District'): 8,
    ('North Beach', 'Golden Gate Park'): 22,
    ('North Beach', 'Union Square'): 7,
    ('Financial District', 'Presidio'): 22,
    ('Financial District', 'Richmond District'): 21,
    ('Financial District', 'North Beach'): 7,
    ('Financial District', 'Golden Gate Park'): 23,
    ('Financial District', 'Union Square'): 9,
    ('Golden Gate Park', 'Presidio'): 11,
    ('Golden Gate Park', 'Richmond District'): 7,
    ('Golden Gate Park', 'North Beach'): 24,
    ('Golden Gate Park', 'Financial District'): 26,
    ('Golden Gate Park', 'Union Square'): 22,
    ('Union Square', 'Presidio'): 24,
    ('Union Square', 'Richmond District'): 20,
    ('Union Square', 'North Beach'): 10,
    ('Union Square', 'Financial District'): 9,
    ('Union Square', 'Golden Gate Park'): 22,
}

# Define friends with their constraints
friends = [
    {'name': 'Jason', 'location': 'Richmond District', 'start': 780, 'end': 1260, 'duration': 90},
    {'name': 'Melissa', 'location': 'North Beach', 'start': 1125, 'end': 1230, 'duration': 45},
    {'name': 'Brian', 'location': 'Financial District', 'start': 585, 'end': 1425, 'duration': 15},
    {'name': 'Elizabeth', 'location': 'Golden Gate Park', 'start': 525, 'end': 1410, 'duration': 105},
    {'name': 'Laura', 'location': 'Union Square', 'start': 810, 'end': 1120, 'duration': 75},
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