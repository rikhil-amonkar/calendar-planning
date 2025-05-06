from z3 import *

# Define travel times (in minutes)
travel_times = {
    ('Golden Gate Park', 'Chinatown'): 23,
    ('Chinatown', 'Golden Gate Park'): 23,
}

# Define a meeting time and duration (in minutes after 9:00 AM)
meeting_time = (960, 105)  # David will be at Chinatown from 4:00 PM to 9:45 PM (960 minutes after midnight)

# Initialize the Z3 solver
solver = Solver()

# Create variables for the meeting start and end times
meeting_start = Int('meeting_start')
meeting_end = Int('meeting_end')

# Add constraints for the meeting based on David's availability
solver.add(meeting_start >= meeting_time[0])  # Must start after David is available (4:00 PM)
solver.add(meeting_end == meeting_start + meeting_time[1])  # Calculate end time

# Add travel time constraints from Golden Gate Park
solver.add(meeting_start >= 540 + travel_times[('Golden Gate Park', 'Chinatown')])  # Must start after 9:00 AM + travel time

# Objective: maximize the meeting time (not strictly necessary in this simple case)
total_meeting_time = meeting_end - meeting_start
solver.maximize(total_meeting_time)

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    start = model[meeting_start].as_long()
    end = model[meeting_end].as_long()
    print("SOLUTION:")
    print(f"Meeting starts at {start} minutes after midnight, ends at {end} minutes after midnight.")
else:
    print("SOLUTION: No valid meeting schedule found.")