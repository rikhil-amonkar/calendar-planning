from z3 import *

# Define the time intervals
start_time = 9 * 60  # 9:00 in minutes
end_time = 17 * 60   # 17:00 in minutes
meeting_duration = 30  # 0.5 hours in minutes

# Define the existing schedules
schedules = {
    'Diana': [(11 * 60 + 30, 12 * 60), (13 * 60, 13 * 60 + 30)],
    'Ethan': [],
    'Janet': [(9 * 60, 10 * 60), (12 * 60 + 30, 13 * 60), (14 * 60, 15 * 60), (15 * 60 + 30, 17 * 60)]
}

# Create a Z3 solver
solver = Solver()

# Define the variables
meeting_start = Int('meeting_start')

# Add constraints
solver.add(meeting_start >= start_time)
solver.add(meeting_start + meeting_duration <= end_time)

# Add constraints for each participant's schedule
for participant, schedule in schedules.items():
    for start, end in schedule:
        solver.add(Or(meeting_start + meeting_duration <= start, meeting_start >= end))

# Add Janet's preference to avoid meetings after 12:00
solver.add(meeting_start + meeting_duration <= 12 * 60)

# Solve the problem
result = solver.check()

if result == sat:
    print("A meeting time has been found:")
    print("Start time: {:.2f}:00".format(solver.model()[meeting_start].as_long() / 60))
else:
    print("No meeting time could be found.")