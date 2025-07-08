# Define the locations and travel times
locations = ['Union Square', 'Golden Gate Park', 'Pacific Heights', 'Presidio', 'Chinatown', 'The Castro']
travel_times = {
    ('Union Square', 'Golden Gate Park'): 22,
    ('Union Square', 'Pacific Heights'): 15,
    ('Union Square', 'Presidio'): 24,
    ('Union Square', 'Chinatown'): 7,
    ('Union Square', 'The Castro'): 19,
    ('Golden Gate Park', 'Union Square'): 22,
    ('Golden Gate Park', 'Pacific Heights'): 16,
    ('Golden Gate Park', 'Presidio'): 11,
    ('Golden Gate Park', 'Chinatown'): 23,
    ('Golden Gate Park', 'The Castro'): 13,
    ('Pacific Heights', 'Union Square'): 12,
    ('Pacific Heights', 'Golden Gate Park'): 15,
    ('Pacific Heights', 'Presidio'): 11,
    ('Pacific Heights', 'Chinatown'): 11,
    ('Pacific Heights', 'The Castro'): 16,
    ('Presidio', 'Union Square'): 22,
    ('Presidio', 'Golden Gate Park'): 12,
    ('Presidio', 'Pacific Heights'): 11,
    ('Presidio', 'Chinatown'): 21,
    ('Presidio', 'The Castro'): 21,
    ('Chinatown', 'Union Square'): 7,
    ('Chinatown', 'Golden Gate Park'): 23,
    ('Chinatown', 'Pacific Heights'): 11,
    ('Chinatown', 'Presidio'): 19,
    ('Chinatown', 'The Castro'): 22,
    ('The Castro', 'Union Square'): 19,
    ('The Castro', 'Golden Gate Park'): 11,
    ('The Castro', 'Pacific Heights'): 16,
    ('The Castro', 'Presidio'): 20,
    ('The Castro', 'Chinatown'): 20,
}

# Define the friends and their availability
friends = {
    'Andrew': {'location': 'Golden Gate Park', 'start': 11*60 + 45, 'end': 14*60 + 30, 'min_meeting_time': 75},
    'Sarah': {'location': 'Pacific Heights', 'start': 16*60 + 15, 'end': 18*60 + 45, 'min_meeting_time': 15},
    'Nancy': {'location': 'Presidio', 'start': 17*60 + 30, 'end': 19*60 + 15, 'min_meeting_time': 60},
    'Rebecca': {'location': 'Chinatown', 'start': 9*60 + 45, 'end': 21*60 + 30, 'min_meeting_time': 90},
    'Robert': {'location': 'The Castro', 'start': 8*60 + 30, 'end': 14*60 + 15, 'min_meeting_time': 30},
}

# Define the manual schedule
schedule = {
    'Union Square': (9*60, 0),
    'Chinatown': (9*60 + 7, 90),
    'The Castro': (9*60 + 7 + 22, 30),
    'Golden Gate Park': (9*60 + 7 + 22 + 13, 75),
    'Pacific Heights': (9*60 + 7 + 22 + 13 + 16, 15),
    'Presidio': (9*60 + 7 + 22 + 13 + 16 + 11, 60)
}

# Verify the schedule
valid_schedule = True
for friend, details in friends.items():
    loc = details['location']
    start = details['start']
    end = details['end']
    min_meeting_time = details['min_meeting_time']
    arrive, duration = schedule[loc]
    if arrive > end - min_meeting_time or arrive + min_meeting_time > end:
        valid_schedule = False
        break

if valid_schedule:
    print("SOLUTION:")
    for loc, (arrive, duration) in sorted(schedule.items(), key=lambda x: x[1][0]):
        print(f"Arrive at {loc} at {arrive//60}:{arrive%60:02d}, stay for {duration} minutes")
else:
    print("No solution found.")