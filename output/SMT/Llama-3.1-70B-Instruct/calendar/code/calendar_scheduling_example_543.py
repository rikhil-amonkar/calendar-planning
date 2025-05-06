from z3 import *

# Define the time slots
start_time = 9 * 60  # 9:00 in minutes
end_time = 17 * 60  # 17:00 in minutes
meeting_duration = 60  # 1 hour in minutes

# Define the existing schedules for James and John
james_schedule = [(11 * 60 + 30, 12 * 60), (14 * 60 + 30, 15 * 60)]
john_schedule = [(9 * 60 + 30, 11 * 60), (11 * 60 + 30, 12 * 60), (12 * 60 + 30, 13 * 60 + 30), (14 * 60 + 30, 16 * 60 + 30)]

# Create a Z3 solver
solver = Solver()

# Create a Z3 variable to represent the start time of the meeting
meeting_start = Int('meeting_start')

# Add constraints to ensure the meeting start time is within the work hours
solver.add(And(meeting_start >= start_time, meeting_start <= end_time - meeting_duration))

# Add constraints to avoid James' schedule
for start, end in james_schedule:
    solver.add(Or(meeting_start + meeting_duration <= start, meeting_start >= end))

# Add constraints to avoid John's schedule
for start, end in john_schedule:
    solver.add(Or(meeting_start + meeting_duration <= start, meeting_start >= end))

# Check if the solver can find a solution
if solver.check() == sat:
    # Get the solution
    model = solver.model()
    meeting_start_time = model[meeting_start].as_long()
    print(f"Meeting can be scheduled from {meeting_start_time // 60}:{meeting_start_time % 60:02} to {(meeting_start_time + meeting_duration) // 60}:{(meeting_start_time + meeting_duration) % 60:02}")
else:
    print("No solution found")