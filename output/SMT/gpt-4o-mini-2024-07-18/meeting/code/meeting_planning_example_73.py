from z3 import *

# Define travel times (in minutes)
travel_time = {
    ('Russian Hill', 'Pacific Heights'): 7,
    ('Pacific Heights', 'Russian Hill'): 7,
}

# Define meeting time constraints
meeting_start_time = 9 * 60  # 9:00 AM in minutes after midnight
barbara_start = (7 * 60) + 15  # 7:15 AM in minutes after midnight
barbara_end = 22 * 60           # 10:00 PM in minutes after midnight
minimum_meeting_time = 60       # minimum meeting time in minutes

# Initialize the Z3 solver
solver = Solver()

# Create variables for meeting start and end times
meeting_start = Int('meeting_start')
meeting_end = Int('meeting_end')

# Add constraints for meeting times
solver.add(meeting_start >= barbara_start)  # Must be after Barbara's start time
solver.add(meeting_end == meeting_start + minimum_meeting_time)  # Calculate end time
solver.add(meeting_end <= barbara_end)      # Must end before Barbara's end time

# Include travel time constraint
solver.add(meeting_start >= meeting_start_time + travel_time[('Russian Hill', 'Pacific Heights')])

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    start = model[meeting_start].as_long()
    end = model[meeting_end].as_long()
    print("SOLUTION:")
    print(f"Meet Barbara: Start at {start} minutes after midnight, End at {end} minutes after midnight")
else:
    print("SOLUTION: No valid meeting schedule found.")