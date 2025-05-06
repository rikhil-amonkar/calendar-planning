from z3 import *

# Define travel times (in minutes)
travel_times = {
    ('The Castro', 'Alamo Square'): 8,
    ('The Castro', 'Richmond District'): 16,
    ('The Castro', 'Financial District'): 21,
    ('The Castro', 'Union Square'): 19,
    ('The Castro', 'Fisherman\'s Wharf'): 24,
    ('The Castro', 'Marina District'): 21,
    ('The Castro', 'Haight-Ashbury'): 6,
    ('The Castro', 'Mission District'): 7,
    ('The Castro', 'Pacific Heights'): 16,
    ('The Castro', 'Golden Gate Park'): 11,
    ('Alamo Square', 'The Castro'): 8,
    ('Alamo Square', 'Richmond District'): 11,
    ('Alamo Square', 'Financial District'): 17,
    ('Alamo Square', 'Union Square'): 14,
    ('Alamo Square', 'Fisherman\'s Wharf'): 19,
    ('Alamo Square', 'Marina District'): 15,
    ('Alamo Square', 'Haight-Ashbury'): 5,
    ('Alamo Square', 'Mission District'): 10,
    ('Alamo Square', 'Pacific Heights'): 10,
    ('Alamo Square', 'Golden Gate Park'): 9,
    ('Richmond District', 'The Castro'): 16,
    ('Richmond District', 'Alamo Square'): 13,
    ('Richmond District', 'Financial District'): 22,
    ('Richmond District', 'Union Square'): 21,
    ('Richmond District', 'Fisherman\'s Wharf'): 18,
    ('Richmond District', 'Marina District'): 9,
    ('Richmond District', 'Haight-Ashbury'): 10,
    ('Richmond District', 'Mission District'): 20,
    ('Richmond District', 'Pacific Heights'): 10,
    ('Richmond District', 'Golden Gate Park'): 9,
    ('Financial District', 'The Castro'): 20,
    ('Financial District', 'Alamo Square'): 17,
    ('Financial District', 'Richmond District'): 21,
    ('Financial District', 'Union Square'): 9,
    ('Financial District', 'Fisherman\'s Wharf'): 10,
    ('Financial District', 'Marina District'): 15,
    ('Financial District', 'Haight-Ashbury'): 19,
    ('Financial District', 'Mission District'): 17,
    ('Financial District', 'Pacific Heights'): 13,
    ('Financial District', 'Golden Gate Park'): 23,
    ('Union Square', 'The Castro'): 17,
    ('Union Square', 'Alamo Square'): 15,
    ('Union Square', 'Richmond District'): 20,
    ('Union Square', 'Financial District'): 9,
    ('Union Square', 'Fisherman\'s Wharf'): 15,
    ('Union Square', 'Marina District'): 18,
    ('Union Square', 'Haight-Ashbury'): 18,
    ('Union Square', 'Mission District'): 14,
    ('Union Square', 'Pacific Heights'): 15,
    ('Union Square', 'Golden Gate Park'): 22,
    ('Fisherman\'s Wharf', 'The Castro'): 27,
    ('Fisherman\'s Wharf', 'Alamo Square'): 21,
    ('Fisherman\'s Wharf', 'Richmond District'): 18,
    ('Fisherman\'s Wharf', 'Financial District'): 11,
    ('Fisherman\'s Wharf', 'Union Square'): 13,
    ('Fisherman\'s Wharf', 'Marina District'): 9,
    ('Fisherman\'s Wharf', 'Haight-Ashbury'): 22,
    ('Fisherman\'s Wharf', 'Mission District'): 22,
    ('Fisherman\'s Wharf', 'Pacific Heights'): 12,
    ('Fisherman\'s Wharf', 'Golden Gate Park'): 25,
    ('Marina District', 'The Castro'): 22,
    ('Marina District', 'Alamo Square'): 15,
    ('Marina District', 'Richmond District'): 11,
    ('Marina District', 'Financial District'): 17,
    ('Marina District', 'Union Square'): 16,
    ('Marina District', 'Fisherman\'s Wharf'): 10,
    ('Marina District', 'Haight-Ashbury'): 16,
    ('Marina District', 'Mission District'): 20,
    ('Marina District', 'Pacific Heights'): 7,
    ('Marina District', 'Golden Gate Park'): 18,
    ('Haight-Ashbury', 'The Castro'): 6,
    ('Haight-Ashbury', 'Alamo Square'): 5,
    ('Haight-Ashbury', 'Richmond District'): 10,
    ('Haight-Ashbury', 'Financial District'): 21,
    ('Haight-Ashbury', 'Union Square'): 19,
    ('Haight-Ashbury', 'Fisherman\'s Wharf'): 23,
    ('Haight-Ashbury', 'Marina District'): 17,
    ('Haight-Ashbury', 'Mission District'): 11,
    ('Haight-Ashbury', 'Pacific Heights'): 12,
    ('Haight-Ashbury', 'Golden Gate Park'): 7,
    ('Mission District', 'The Castro'): 7,
    ('Mission District', 'Alamo Square'): 11,
    ('Mission District', 'Richmond District'): 20,
    ('Mission District', 'Financial District'): 15,
    ('Mission District', 'Union Square'): 15,
    ('Mission District', 'Fisherman\'s Wharf'): 22,
    ('Mission District', 'Marina District'): 19,
    ('Mission District', 'Haight-Ashbury'): 12,
    ('Mission District', 'Pacific Heights'): 16,
    ('Mission District', 'Golden Gate Park'): 17,
    ('Pacific Heights', 'The Castro'): 16,
    ('Pacific Heights', 'Alamo Square'): 10,
    ('Pacific Heights', 'Richmond District'): 12,
    ('Pacific Heights', 'Financial District'): 13,
    ('Pacific Heights', 'Union Square'): 12,
    ('Pacific Heights', 'Fisherman\'s Wharf'): 13,
    ('Pacific Heights', 'Marina District'): 6,
    ('Pacific Heights', 'Haight-Ashbury'): 11,
    ('Pacific Heights', 'Mission District'): 15,
    ('Pacific Heights', 'Golden Gate Park'): 15,
    ('Golden Gate Park', 'The Castro'): 13,
    ('Golden Gate Park', 'Alamo Square'): 9,
    ('Golden Gate Park', 'Richmond District'): 7,
    ('Golden Gate Park', 'Financial District'): 26,
    ('Golden Gate Park', 'Union Square'): 22,
    ('Golden Gate Park', 'Fisherman\'s Wharf'): 24,
    ('Golden Gate Park', 'Marina District'): 16,
    ('Golden Gate Park', 'Haight-Ashbury'): 7,
    ('Golden Gate Park', 'Mission District'): 17,
    ('Golden Gate Park', 'Pacific Heights'): 16,
}

# Define meeting times and durations (in minutes after 9:00 AM)
meeting_times = {
    'William': (915, 60),       # 3:15 PM - 5:15 PM
    'Joshua': (420, 15),        # 7:00 AM - 8:00 PM
    'Joseph': (675, 15),        # 11:15 AM - 1:30 PM
    'David': (1050, 45),        # 4:45 PM - 7:15 PM
    'Brian': (885, 105),        # 1:45 PM - 8:45 PM
    'Karen': (690, 15),         # 11:30 AM - 6:30 PM
    'Anthony': (435, 30),       # 7:15 AM - 10:30 AM
    'Matthew': (315, 120),      # 5:15 PM - 7:15 PM
    'Helen': (480, 75),         # 8:00 AM - 12:00 PM
    'Jeffrey': (1140, 60),      # 7:00 PM - 9:30 PM
}

# Minimum meeting durations (in minutes)
minimum_durations = {
    'William': 60,
    'Joshua': 15,
    'Joseph': 15,
    'David': 45,
    'Brian': 105,
    'Karen': 15,
    'Anthony': 30,
    'Matthew': 120,
    'Helen': 75,
    'Jeffrey': 60,
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

# Travel constraints from The Castro (arrival at 9:00 AM)
travel_times_to_friends = {
    'William': travel_times[('The Castro', 'Alamo Square')],
    'Joshua': travel_times[('The Castro', 'Richmond District')],
    'Joseph': travel_times[('The Castro', 'Financial District')],
    'David': travel_times[('The Castro', 'Union Square')],
    'Brian': travel_times[('The Castro', 'Fisherman\'s Wharf')],
    'Karen': travel_times[('The Castro', 'Marina District')],
    'Anthony': travel_times[('The Castro', 'Haight-Ashbury')],
    'Matthew': travel_times[('The Castro', 'Mission District')],
    'Helen': travel_times[('The Castro', 'Pacific Heights')],
    'Jeffrey': travel_times[('The Castro', 'Golden Gate Park')],
}

# Add constraints for ensuring enough time to meet each friend after travel
for friend, travel_time in travel_times_to_friends.items():
    solver.add(meeting_start[friend] >= travel_time)  # Must start after travel time

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