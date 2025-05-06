from z3 import *

# Define travel times (in minutes)
travel_times = {
    ('Embarcadero', 'Fisherman\'s Wharf'): 6,
    ('Embarcadero', 'Financial District'): 5,
    ('Embarcadero', 'Russian Hill'): 8,
    ('Embarcadero', 'Marina District'): 12,
    ('Embarcadero', 'Richmond District'): 21,
    ('Embarcadero', 'Pacific Heights'): 11,
    ('Embarcadero', 'Haight-Ashbury'): 21,
    ('Embarcadero', 'Presidio'): 20,
    ('Embarcadero', 'Nob Hill'): 10,
    ('Embarcadero', 'The Castro'): 25,
    ('Fisherman\'s Wharf', 'Embarcadero'): 8,
    ('Fisherman\'s Wharf', 'Financial District'): 11,
    ('Fisherman\'s Wharf', 'Russian Hill'): 7,
    ('Fisherman\'s Wharf', 'Marina District'): 9,
    ('Fisherman\'s Wharf', 'Richmond District'): 18,
    ('Fisherman\'s Wharf', 'Pacific Heights'): 12,
    ('Fisherman\'s Wharf', 'Haight-Ashbury'): 22,
    ('Fisherman\'s Wharf', 'Presidio'): 17,
    ('Fisherman\'s Wharf', 'Nob Hill'): 11,
    ('Fisherman\'s Wharf', 'The Castro'): 27,
    ('Financial District', 'Embarcadero'): 4,
    ('Financial District', 'Fisherman\'s Wharf'): 10,
    ('Financial District', 'Russian Hill'): 11,
    ('Financial District', 'Marina District'): 15,
    ('Financial District', 'Richmond District'): 21,
    ('Financial District', 'Pacific Heights'): 13,
    ('Financial District', 'Haight-Ashbury'): 19,
    ('Financial District', 'Presidio'): 22,
    ('Financial District', 'Nob Hill'): 8,
    ('Financial District', 'The Castro'): 20,
    ('Russian Hill', 'Embarcadero'): 8,
    ('Russian Hill', 'Fisherman\'s Wharf'): 7,
    ('Russian Hill', 'Financial District'): 11,
    ('Russian Hill', 'Marina District'): 7,
    ('Russian Hill', 'Richmond District'): 14,
    ('Russian Hill', 'Pacific Heights'): 7,
    ('Russian Hill', 'Haight-Ashbury'): 17,
    ('Russian Hill', 'Presidio'): 14,
    ('Russian Hill', 'Nob Hill'): 5,
    ('Russian Hill', 'The Castro'): 21,
    ('Marina District', 'Embarcadero'): 14,
    ('Marina District', 'Fisherman\'s Wharf'): 10,
    ('Marina District', 'Financial District'): 17,
    ('Marina District', 'Russian Hill'): 8,
    ('Marina District', 'Richmond District'): 9,
    ('Marina District', 'Pacific Heights'): 6,
    ('Marina District', 'Haight-Ashbury'): 16,
    ('Marina District', 'Presidio'): 10,
    ('Marina District', 'Nob Hill'): 12,
    ('Marina District', 'The Castro'): 22,
    ('Richmond District', 'Embarcadero'): 19,
    ('Richmond District', 'Fisherman\'s Wharf'): 18,
    ('Richmond District', 'Financial District'): 22,
    ('Richmond District', 'Russian Hill'): 13,
    ('Richmond District', 'Marina District'): 9,
    ('Richmond District', 'Pacific Heights'): 10,
    ('Richmond District', 'Haight-Ashbury'): 10,
    ('Richmond District', 'Presidio'): 7,
    ('Richmond District', 'Nob Hill'): 17,
    ('Richmond District', 'The Castro'): 16,
    ('Pacific Heights', 'Embarcadero'): 10,
    ('Pacific Heights', 'Fisherman\'s Wharf'): 13,
    ('Pacific Heights', 'Financial District'): 13,
    ('Pacific Heights', 'Russian Hill'): 7,
    ('Pacific Heights', 'Marina District'): 6,
    ('Pacific Heights', 'Richmond District'): 12,
    ('Pacific Heights', 'Haight-Ashbury'): 11,
    ('Pacific Heights', 'Presidio'): 11,
    ('Pacific Heights', 'Nob Hill'): 8,
    ('Pacific Heights', 'The Castro'): 16,
    ('Haight-Ashbury', 'Embarcadero'): 20,
    ('Haight-Ashbury', 'Fisherman\'s Wharf'): 23,
    ('Haight-Ashbury', 'Financial District'): 21,
    ('Haight-Ashbury', 'Russian Hill'): 17,
    ('Haight-Ashbury', 'Marina District'): 17,
    ('Haight-Ashbury', 'Richmond District'): 10,
    ('Haight-Ashbury', 'Pacific Heights'): 12,
    ('Haight-Ashbury', 'Presidio'): 15,
    ('Haight-Ashbury', 'Nob Hill'): 15,
    ('Haight-Ashbury', 'The Castro'): 6,
    ('Presidio', 'Embarcadero'): 20,
    ('Presidio', 'Fisherman\'s Wharf'): 19,
    ('Presidio', 'Financial District'): 23,
    ('Presidio', 'Russian Hill'): 14,
    ('Presidio', 'Marina District'): 11,
    ('Presidio', 'Richmond District'): 7,
    ('Presidio', 'Pacific Heights'): 11,
    ('Presidio', 'Haight-Ashbury'): 15,
    ('Presidio', 'Nob Hill'): 18,
    ('Presidio', 'The Castro'): 21,
    ('Nob Hill', 'Embarcadero'): 9,
    ('Nob Hill', 'Fisherman\'s Wharf'): 10,
    ('Nob Hill', 'Financial District'): 9,
    ('Nob Hill', 'Russian Hill'): 5,
    ('Nob Hill', 'Marina District'): 11,
    ('Nob Hill', 'Richmond District'): 14,
    ('Nob Hill', 'Pacific Heights'): 8,
    ('Nob Hill', 'Haight-Ashbury'): 13,
    ('Nob Hill', 'Presidio'): 17,
    ('Nob Hill', 'The Castro'): 17,
    ('The Castro', 'Embarcadero'): 22,
    ('The Castro', 'Fisherman\'s Wharf'): 24,
    ('The Castro', 'Financial District'): 21,
    ('The Castro', 'Russian Hill'): 18,
    ('The Castro', 'Marina District'): 21,
    ('The Castro', 'Richmond District'): 16,
    ('The Castro', 'Pacific Heights'): 16,
    ('The Castro', 'Haight-Ashbury'): 6,
    ('The Castro', 'Presidio'): 20,
    ('The Castro', 'Nob Hill'): 16,
}

# Define meeting times and durations (in minutes after 9:00 AM)
meeting_times = {
    'Stephanie': (930, 30),    # 3:30 PM - 10:00 PM
    'Lisa': (645, 15),          # 10:45 AM - 5:15 PM
    'Melissa': (900, 120),      # 5:00 PM - 9:45 PM
    'Betty': (645, 60),         # 10:45 AM - 2:15 PM
    'Sarah': (255, 105),        # 4:15 PM - 7:30 PM
    'Daniel': (390, 60),        # 6:30 PM - 9:45 PM
    'Joshua': (540, 15),        # 9:00 AM - 3:30 PM
    'Joseph': (420, 45),        # 7:00 AM - 1:00 PM
    'Andrew': (1140, 105),      # 7:45 PM - 10:00 PM
    'John': (75, 45),           # 1:15 PM - 7:45 PM
}

# Minimum meeting durations (in minutes)
minimum_durations = {
    'Stephanie': 30,
    'Lisa': 15,
    'Melissa': 120,
    'Betty': 60,
    'Sarah': 105,
    'Daniel': 60,
    'Joshua': 15,
    'Joseph': 45,
    'Andrew': 105,
    'John': 45,
}

# Initialize the Z3 solver
solver = Solver()

# Create variables for meeting start and end times
meeting_start = {friend: Int(f'{friend}_start') for friend in meeting_times}
meeting_end = {friend: Int(f'{friend}_end') for friend in meeting_times}

# Add constraints for meeting times based on friends' availability
for friend in meeting_times.keys():
    start_time, _ = meeting_times[friend]
    solver.add(meeting_start[friend] >= start_time)  # Must be after their start time
    solver.add(meeting_end[friend] == meeting_start[friend] + minimum_durations[friend])  # Calculate end time

# Travel constraints from Embarcadero (arrival at 9:00 AM)
travel_times_to_friends = {
    'Stephanie': travel_times[('Embarcadero', 'Fisherman\'s Wharf')],
    'Lisa': travel_times[('Embarcadero', 'Financial District')],
    'Melissa': travel_times[('Embarcadero', 'Russian Hill')],
    'Betty': travel_times[('Embarcadero', 'Marina District')],
    'Sarah': travel_times[('Embarcadero', 'Richmond District')],
    'Daniel': travel_times[('Embarcadero', 'Pacific Heights')],
    'Joshua': travel_times[('Embarcadero', 'Haight-Ashbury')],
    'Joseph': travel_times[('Embarcadero', 'Presidio')],
    'Andrew': travel_times[('Embarcadero', 'Nob Hill')],
    'John': travel_times[('Embarcadero', 'The Castro')],
}

# Add constraints for ensuring enough time to meet each friend
for friend, travel_time in travel_times_to_friends.items():
    solver.add(meeting_start[friend] >= travel_time)  # Meeting can only start after travel

# Objective: maximize total meeting time
total_meeting_time = Sum([meeting_end[friend] - meeting_start[friend] for friend in meeting_times])
solver.maximize(total_meeting_time)

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    print("SOLUTION:")
    for friend in meeting_times.keys():
        start = model[meeting_start[friend]].as_long() 
        end = model[meeting_end[friend]].as_long()
        print(f"{friend}: Start at {start} minutes after 9:00 AM, End at {end} minutes after 9:00 AM")
else:
    print("SOLUTION: No valid meeting schedule found.")