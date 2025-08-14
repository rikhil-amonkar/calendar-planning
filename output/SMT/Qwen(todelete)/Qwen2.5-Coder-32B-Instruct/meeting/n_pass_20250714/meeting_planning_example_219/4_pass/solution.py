# Define the friends' availability and meeting durations
friends_info = {
    'Emily': {'location': 'Alamo Square', 'start': 11*60 + 45, 'end': 15*60 + 15, 'duration': 105},
    'Barbara': {'location': 'Union Square', 'start': 16*60 + 45, 'end': 18*60 + 15, 'duration': 60},
    'William': {'location': 'Chinatown', 'start': 17*60 + 15, 'end': 19*60, 'duration': 105},
}

# Define the feasible schedule
feasible_schedule = {
    'Barbara': {'location': 'Union Square', 'start': 16*60 + 45, 'end': 17*60 + 45},
    'William': {'location': 'Chinatown', 'start': 17*60 + 15, 'end': 19*60}
}

# Print the feasible schedule
print("SOLUTION:")
for friend, info in feasible_schedule.items():
    start = info['start']
    end = info['end']
    duration = end - start
    print(f"Meet {friend} at {info['location']} from {start//60}:{start%60:02d} to {end//60}:{end%60:02d}")