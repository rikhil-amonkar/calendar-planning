# Define the friends' availability and meeting durations
friends_info = {
    'Emily': {'location': 'Alamo Square', 'start': 11*60 + 45, 'end': 15*60 + 15, 'duration': 105},
    'Barbara': {'location': 'Union Square', 'start': 16*60 + 45, 'end': 18*60 + 15, 'duration': 60},
    'William': {'location': 'Chinatown', 'start': 17*60 + 15, 'end': 19*60, 'duration': 105},
}

# Define the travel times in minutes
travel_times = {
    ('The Castro', 'Alamo Square'): 8,
    ('The Castro', 'Union Square'): 19,
    ('The Castro', 'Chinatown'): 20,
    ('Alamo Square', 'The Castro'): 8,
    ('Alamo Square', 'Union Square'): 14,
    ('Alamo Square', 'Chinatown'): 16,
    ('Union Square', 'The Castro'): 19,
    ('Union Square', 'Alamo Square'): 15,
    ('Union Square', 'Chinatown'): 7,
    ('Chinatown', 'The Castro'): 22,
    ('Chinatown', 'Alamo Square'): 17,
    ('Chinatown', 'Union Square'): 7,
}

# Function to check if a schedule is feasible
def is_feasible(schedule):
    arrival_times = {'The Castro': 9*60}
    for friend, info in schedule.items():
        loc = info['location']
        start = info['start']
        duration = info['duration']
        if loc not in arrival_times:
            return False
        if arrival_times[loc] > start:
            return False
        arrival_times[loc] = start
        next_loc = friends_info[friend]['location']
        travel_time = travel_times[(loc, next_loc)]
        if arrival_times[loc] + duration + travel_time > friends_info[friend]['end']:
            return False
        arrival_times[next_loc] = arrival_times[loc] + duration + travel_time
    return True

# Check all pairs of friends
friends = list(friends_info.keys())
feasible_schedule = None
for i in range(len(friends)):
    for j in range(i + 1, len(friends)):
        schedule = {friends[i]: friends_info[friends[i]], friends[j]: friends_info[friends[j]]}
        if is_feasible(schedule):
            feasible_schedule = schedule
            break
    if feasible_schedule:
        break

# Print the feasible schedule
if feasible_schedule:
    print("SOLUTION:")
    for friend, info in feasible_schedule.items():
        start = info['start']
        end = start + info['duration']
        print(f"Meet {friend} at {info['location']} from {start//60}:{start%60:02d} to {end//60}:{end%60:02d}")
else:
    print("No solution found.")