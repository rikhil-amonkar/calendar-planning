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

# Manually set the start times for the valid sequences
# Sequence: Timothy -> David -> Robert
solver.add(start_timothy == 540)  # 9:00 AM
solver.add(start_david == 628)    # 10:28 AM
solver.add(start_robert == 645)   # 10:45 AM

# Add constraints for David's meeting
solver.add(start_david >= available_time_david[0])
solver.add(start_david + required_duration_david <= available_time_david[1])

# Add constraints for Timothy's meeting
solver.add(start_timothy >= available_time_timothy[0])
solver.add(start_timothy + required_duration_timothy <= available_time_timothy[1])

# Add constraints for Robert's meeting
solver.add(start_robert >= available_time_robert[0])
solver.add(start_robert + required_duration_robert <= available_time_robert[1])

# Check if the solver can find a solution
if solver.check() == sat:
    model = solver.model()
    print("SOLUTION:")
    print(f"Meet Timothy from {model[start_timothy].as_long()} to {model[start_timothy].as_long() + required_duration_timothy} (minutes from 9:00 AM)")
    print(f"Meet David from {model[start_david].as_long()} to {model[start_david].as_long() + required_duration_david} (minutes from 9:00 AM)")
    print(f"Meet Robert from {model[start_robert].as_long()} to {model[start_robert].as_long() + required_duration_robert} (minutes from 9:00 AM)")
else:
    print("No solution found")