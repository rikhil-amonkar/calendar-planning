from z3 import *

# Define travel times (in minutes)
travel_times = {
    ('Chinatown', 'Embarcadero'): 5,
    ('Chinatown', 'Pacific Heights'): 10,
    ('Chinatown', 'Russian Hill'): 7,
    ('Chinatown', 'Haight-Ashbury'): 19,
    ('Chinatown', 'Golden Gate Park'): 23,
    ('Chinatown', 'Fisherman\'s Wharf'): 8,
    ('Chinatown', 'Sunset District'): 29,
    ('Chinatown', 'The Castro'): 22,
    ('Embarcadero', 'Chinatown'): 7,
    ('Embarcadero', 'Pacific Heights'): 11,
    ('Embarcadero', 'Russian Hill'): 8,
    ('Embarcadero', 'Haight-Ashbury'): 21,
    ('Embarcadero', 'Golden Gate Park'): 25,
    ('Embarcadero', 'Fisherman\'s Wharf'): 6,
    ('Embarcadero', 'Sunset District'): 30,
    ('Embarcadero', 'The Castro'): 25,
    ('Pacific Heights', 'Chinatown'): 11,
    ('Pacific Heights', 'Embarcadero'): 10,
    ('Pacific Heights', 'Russian Hill'): 7,
    ('Pacific Heights', 'Haight-Ashbury'): 11,
    ('Pacific Heights', 'Golden Gate Park'): 15,
    ('Pacific Heights', 'Fisherman\'s Wharf'): 13,
    ('Pacific Heights', 'Sunset District'): 21,
    ('Pacific Heights', 'The Castro'): 16,
    ('Russian Hill', 'Chinatown'): 9,
    ('Russian Hill', 'Embarcadero'): 8,
    ('Russian Hill', 'Pacific Heights'): 7,
    ('Russian Hill', 'Haight-Ashbury'): 17,
    ('Russian Hill', 'Golden Gate Park'): 21,
    ('Russian Hill', 'Fisherman\'s Wharf'): 7,
    ('Russian Hill', 'Sunset District'): 23,
    ('Russian Hill', 'The Castro'): 21,
    ('Haight-Ashbury', 'Chinatown'): 19,
    ('Haight-Ashbury', 'Embarcadero'): 20,
    ('Haight-Ashbury', 'Pacific Heights'): 12,
    ('Haight-Ashbury', 'Russian Hill'): 17,
    ('Haight-Ashbury', 'Golden Gate Park'): 7,
    ('Haight-Ashbury', 'Fisherman\'s Wharf'): 23,
    ('Haight-Ashbury', 'Sunset District'): 15,
    ('Haight-Ashbury', 'The Castro'): 6,
    ('Golden Gate Park', 'Chinatown'): 23,
    ('Golden Gate Park', 'Embarcadero'): 25,
    ('Golden Gate Park', 'Pacific Heights'): 16,
    ('Golden Gate Park', 'Russian Hill'): 19,
    ('Golden Gate Park', 'Haight-Ashbury'): 7,
    ('Golden Gate Park', 'Fisherman\'s Wharf'): 24,
    ('Golden Gate Park', 'Sunset District'): 10,
    ('Golden Gate Park', 'The Castro'): 13,
    ('Fisherman\'s Wharf', 'Chinatown'): 12,
    ('Fisherman\'s Wharf', 'Embarcadero'): 8,
    ('Fisherman\'s Wharf', 'Pacific Heights'): 12,
    ('Fisherman\'s Wharf', 'Russian Hill'): 7,
    ('Fisherman\'s Wharf', 'Haight-Ashbury'): 22,
    ('Fisherman\'s Wharf', 'Golden Gate Park'): 25,
    ('Fisherman\'s Wharf', 'Sunset District'): 27,
    ('Fisherman\'s Wharf', 'The Castro'): 27,
    ('Sunset District', 'Chinatown'): 30,
    ('Sunset District', 'Embarcadero'): 30,
    ('Sunset District', 'Pacific Heights'): 21,
    ('Sunset District', 'Russian Hill'): 24,
    ('Sunset District', 'Haight-Ashbury'): 15,
    ('Sunset District', 'Golden Gate Park'): 11,
    ('Sunset District', 'Fisherman\'s Wharf'): 29,
    ('Sunset District', 'The Castro'): 17,
    ('The Castro', 'Chinatown'): 22,
    ('The Castro', 'Embarcadero'): 22,
    ('The Castro', 'Pacific Heights'): 16,
    ('The Castro', 'Russian Hill'): 18,
    ('The Castro', 'Haight-Ashbury'): 6,
    ('The Castro', 'Golden Gate Park'): 11,
    ('The Castro', 'Fisherman\'s Wharf'): 24,
    ('The Castro', 'Sunset District'): 17,
}

# Define meeting times and durations (in minutes after 9:00 AM)
meeting_times = {
    'Richard': (915, 90),   # Available from 3:15 PM (915 minutes after midnight)
    'Mark': (900, 45),      # Available from 3:00 PM (900 minutes after midnight)
    'Matthew': (1050, 90),  # Available from 5:30 PM (1050 minutes after midnight)
    'Rebecca': (840, 60),   # Available from 2:45 PM (840 minutes after midnight)
    'Melissa': (825, 90),   # Available from 1:45 PM (825 minutes after midnight)
    'Margaret': (840, 15),   # Available from 2:45 PM (840 minutes after midnight)
    'Emily': (915, 45),      # Available from 3:45 PM (915 minutes after midnight)
    'George': (840, 75)      # Available from 2:00 PM (840 minutes after midnight)
}

# Initialize the Z3 solver
solver = Solver()

# Create variables for meeting start and end times
meeting_start = {friend: Int(f'{friend}_start') for friend in meeting_times}
meeting_end = {friend: Int(f'{friend}_end') for friend in meeting_times}

# Add constraints for meeting times based on friends' availability
for friend, (start_time, duration) in meeting_times.items():
    solver.add(meeting_start[friend] >= start_time)  # Must start after their available time
    solver.add(meeting_end[friend] == meeting_start[friend] + duration)  # Calculate end time

# Travel time constraints from Chinatown (arrival at 9:00 AM)
travel_times_to_friends = {
    'Richard': travel_times[('Chinatown', 'Embarcadero')],
    'Mark': travel_times[('Chinatown', 'Pacific Heights')],
    'Matthew': travel_times[('Chinatown', 'Russian Hill')],
    'Rebecca': travel_times[('Chinatown', 'Haight-Ashbury')],
    'Melissa': travel_times[('Chinatown', 'Golden Gate Park')],
    'Margaret': travel_times[('Chinatown', 'Fisherman\'s Wharf')],
    'Emily': travel_times[('Chinatown', 'Sunset District')],
    'George': travel_times[('Chinatown', 'The Castro')],
}

# Add constraints for ensuring enough time to meet each friend after traveling
for friend, travel_time in travel_times_to_friends.items():
    solver.add(meeting_start[friend] >= 540 + travel_time)  # Must start after 9:00 AM + travel time (540 = 9:00 AM in minutes)

# Objective: maximize total meeting time
total_meeting_time = Sum([meeting_end[friend] - meeting_start[friend] for friend in meeting_times])
solver.maximize(total_meeting_time)

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    print("SOLUTION:")
    for friend in meeting_times:
        start = model[meeting_start[friend]].as_long()
        end = model[meeting_end[friend]].as_long()
        print(f"{friend}: Start at {start} minutes after midnight, End at {end} minutes after midnight")
else:
    print("SOLUTION: No valid meeting schedule found.")