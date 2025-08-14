# Define the travel times in minutes
travel_times = {
    ('Union Square', 'Nob Hill'): 9,
    ('Union Square', 'Haight-Ashbury'): 18,
    ('Union Square', 'Chinatown'): 7,
    ('Union Square', 'Marina District'): 18,
    ('Nob Hill', 'Union Square'): 7,
    ('Nob Hill', 'Haight-Ashbury'): 13,
    ('Nob Hill', 'Chinatown'): 6,
    ('Nob Hill', 'Marina District'): 11,
    ('Haight-Ashbury', 'Union Square'): 17,
    ('Haight-Ashbury', 'Nob Hill'): 15,
    ('Haight-Ashbury', 'Chinatown'): 19,
    ('Haight-Ashbury', 'Marina District'): 17,
    ('Chinatown', 'Union Square'): 7,
    ('Chinatown', 'Nob Hill'): 8,
    ('Chinatown', 'Haight-Ashbury'): 19,
    ('Chinatown', 'Marina District'): 12,
    ('Marina District', 'Union Square'): 16,
    ('Marina District', 'Nob Hill'): 12,
    ('Marina District', 'Haight-Ashbury'): 16,
    ('Marina District', 'Chinatown'): 16,
}

# Define the availability and required meeting durations
availabilities = {
    'Karen': ((9*60 + 15, 9*60 + 45), 30),
    'Joseph': ((12*60 + 30, 19*60 + 45), 90),
    'Sandra': ((7*60 + 15, 19*60 + 15), 75),
    'Nancy': ((11*60, 20*60 + 15), 105)
}

# Initial time and location
current_time = 9 * 60  # 9:00 AM in minutes
current_location = 'Union Square'

# Schedule
schedule = []

# Meet Sandra first
sandra_start = max(current_time, availabilities['Sandra'][0])
sandra_end = sandra_start + availabilities['Sandra'][1]
current_time = sandra_end
current_location = 'Chinatown'
schedule.append(('Sandra', sandra_start))

# Travel to Nancy
nancy_start = current_time + travel_times[(current_location, 'Marina District')]
nancy_end = nancy_start + availabilities['Nancy'][1]
current_time = nancy_end
current_location = 'Marina District'
schedule.append(('Nancy', nancy_start))

# Travel to Joseph
joseph_start = current_time + travel_times[(current_location, 'Haight-Ashbury')]
joseph_end = joseph_start + availabilities['Joseph'][1]
current_time = joseph_end
current_location = 'Haight-Ashbury'
schedule.append(('Joseph', joseph_start))

# Travel to Karen
karen_start = current_time + travel_times[(current_location, 'Nob Hill')]
karen_end = karen_start + availabilities['Karen'][1]
current_time = karen_end
current_location = 'Nob Hill'
schedule.append(('Karen', karen_start))

# Print the solution
print("SOLUTION:")
for name, start_time in sorted(schedule, key=lambda x: x[1]):
    start_hour = start_time // 60
    start_minute = start_time % 60
    print(f"Meet {name} at {start_hour:02}:{start_minute:02}")