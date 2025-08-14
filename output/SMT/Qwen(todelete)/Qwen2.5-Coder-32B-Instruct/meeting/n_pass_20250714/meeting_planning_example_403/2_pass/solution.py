from z3 import *

# Define the locations
locations = ['Union Square', 'Golden Gate Park', 'Pacific Heights', 'Presidio', 'Chinatown', 'The Castro']

# Define the travel times between locations
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

# Create a solver instance
solver = Solver()

# Define variables for the time spent at each location
time_at_location = {loc: Int(f"time_at_{loc}") for loc in locations}

# Define variables for the arrival time at each location
arrival_time = {loc: Int(f"arrival_at_{loc}") for loc in locations}

# Set the initial arrival time at Union Square
solver.add(arrival_time['Union Square'] == 9*60)

# Add constraints for the time spent at each location
for loc in locations:
    solver.add(time_at_location[loc] >= 0)

# Add constraints for the arrival times at each location
for (loc1, loc2), time in travel_times.items():
    solver.add(arrival_time[loc2] >= arrival_time[loc1] + time_at_location[loc1] + time)

# Add constraints for meeting friends
for friend, details in friends.items():
    loc = details['location']
    start = details['start']
    end = details['end']
    min_meeting_time = details['min_meeting_time']
    
    # Ensure we arrive at the location before the friend leaves
    solver.add(arrival_time[loc] <= end - min_meeting_time)
    
    # Ensure we stay long enough to meet the friend
    solver.add(time_at_location[loc] >= min_meeting_time)
    
    # Ensure we leave after the friend arrives
    solver.add(arrival_time[loc] + min_meeting_time <= end)

# Ensure we meet exactly 5 friends
meet_friends = {friend: Bool(f"meet_{friend}") for friend in friends}
for friend, details in friends.items():
    loc = details['location']
    solver.add(meet_friends[friend] == (time_at_location[loc] >= details['min_meeting_time']))

# Sum of all meet_friends should be exactly 5
solver.add(Sum([If(meet_friends[friend], 1, 0) for friend in friends]) == 5)

# Check if the problem is solvable
if solver.check() == sat:
    model = solver.model()
    schedule = {}
    for loc in locations:
        schedule[loc] = model[arrival_time[loc]].as_long(), model[time_at_location[loc]].as_long()
    
    print("SOLUTION:")
    for loc, (arrive, duration) in sorted(schedule.items(), key=lambda x: x[1][0]):
        print(f"Arrive at {loc} at {arrive//60}:{arrive%60:02d}, stay for {duration} minutes")
else:
    print("No solution found.")