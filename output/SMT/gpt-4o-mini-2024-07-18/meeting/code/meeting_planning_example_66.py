from z3 import *

# Define travel times (in minutes)
travel_times = {
    ('Nob Hill', 'Presidio'): 17,
    ('Presidio', 'Nob Hill'): 18,
}

# Define meeting time and duration (in minutes after 9:00 AM)
meeting_time = (675, 120)  # Robert will be at Presidio from 11:15 AM (675 minutes after midnight)

# Initialize the Z3 solver
solver = Solver()

# Create variables for meeting start and end times
meeting_start = Int('meeting_start')
meeting_end = Int('meeting_end')

# Add constraints for the meeting based on Robert's availability
solver.add(meeting_start >= meeting_time[0])  # Must start after Robert is available
solver.add(meeting_end == meeting_start + meeting_time[1])  # Calculate end time

# Add travel time constraints from Nob Hill
solver.add(meeting_start >= 540 + travel_times[('Nob Hill', 'Presidio')])  # Must start after 9:00 AM + travel time (540 = 9:00 AM in minutes)

# Objective: maximize total meeting time (though there's only one meeting here)
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