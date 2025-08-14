from z3 import *

# Define the solver
solver = Solver()

# Define variables for the start times of each meeting
start_david = Int('start_david')
start_timothy = Int('start_timothy')
start_robert = Int('start_robert')

# Define constants for the travel times in minutes
travel_times = {
    ('Financial District', 'Fisherman\'s Wharf'): 10,
    ('Financial District', 'Pacific Heights'): 13,
    ('Financial District', 'Mission District'): 17,
    ('Fisherman\'s Wharf', 'Financial District'): 11,
    ('Fisherman\'s Wharf', 'Pacific Heights'): 12,
    ('Fisherman\'s Wharf', 'Mission District'): 22,
    ('Pacific Heights', 'Financial District'): 13,
    ('Pacific Heights', 'Fisherman\'s Wharf'): 13,
    ('Pacific Heights', 'Mission District'): 15,
    ('Mission District', 'Financial District'): 17,
    ('Mission District', 'Fisherman\'s Wharf'): 22,
    ('Mission District', 'Pacific Heights'): 16
}

# Define the available time windows for each friend in minutes from 9:00 AM
available_time_david = (10 * 60 + 45, 15 * 60 + 30)  # 10:45 AM to 3:30 PM
available_time_timothy = (9 * 60, 15 * 60 + 30)       # 9:00 AM to 3:30 PM
available_time_robert = (12 * 60 + 15, 19 * 60 + 45)   # 12:15 PM to 7:45 PM

# Define the required meeting durations in minutes
required_duration_david = 15
required_duration_timothy = 75
required_duration_robert = 90

# Constraints for David's meeting
solver.add(start_david >= available_time_david[0])
solver.add(start_david + required_duration_david <= available_time_david[1])

# Constraints for Timothy's meeting
solver.add(start_timothy >= available_time_timothy[0])
solver.add(start_timothy + required_duration_timothy <= available_time_timothy[1])

# Constraints for Robert's meeting
solver.add(start_robert >= available_time_robert[0])
solver.add(start_robert + required_duration_robert <= available_time_robert[1])

# Define possible sequences of meetings
sequences = [
    (start_timothy, start_david, start_robert),
    (start_timothy, start_robert, start_david),
    (start_david, start_timothy, start_robert),
    (start_david, start_robert, start_timothy),
    (start_robert, start_timothy, start_david),
    (start_robert, start_david, start_timothy)
]

# Function to add constraints for a given sequence
def add_sequence_constraints(seq):
    s1, s2, s3 = seq
    solver.push()
    solver.add(s1 + required_duration_timothy + travel_times[('Financial District', 'Fisherman\'s Wharf')] <= s2)
    solver.add(s2 + required_duration_david + travel_times[('Fisherman\'s Wharf', 'Pacific Heights')] <= s3)
    solver.add(s3 + required_duration_robert <= available_time_robert[1])
    return solver.check() == sat, solver.model()

# Check each sequence
for seq in sequences:
    is_sat, model = add_sequence_constraints(seq)
    if is_sat:
        print("SOLUTION:")
        print(f"Meet Timothy from {model[seq[0]].as_long()} to {model[seq[0]].as_long() + required_duration_timothy} (minutes from 9:00 AM)")
        print(f"Meet David from {model[seq[1]].as_long()} to {model[seq[1]].as_long() + required_duration_david} (minutes from 9:00 AM)")
        print(f"Meet Robert from {model[seq[2]].as_long()} to {model[seq[2]].as_long() + required_duration_robert} (minutes from 9:00 AM)")
        break
else:
    print("No solution found")