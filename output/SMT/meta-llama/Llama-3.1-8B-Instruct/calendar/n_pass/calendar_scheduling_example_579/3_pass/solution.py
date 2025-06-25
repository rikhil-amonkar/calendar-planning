from z3 import *

# Define the variables
day = 'Monday'
start_time = 9 * 60  # 9:00 in minutes
end_time = 17 * 60  # 17:00 in minutes
meeting_duration = 30  # 30 minutes
meeting_start = Int('meeting_start')
meeting_end = Int('meeting_end')

# Define the constraints for Christine
christine_meetings = [11 * 60, 15 * 60]  # 11:00 and 15:00 in minutes
christine_constraints = [And(meeting_start >= 9 * 60, meeting_start <= 11 * 60),
                         And(meeting_start >= 15 * 60, meeting_start <= 17 * 60),
                         meeting_end <= 11 * 60 + 30, meeting_end <= 15 * 60 + 30]

# Define the constraints for Helen
helen_blocked = [9.5 * 60, 10.5 * 60, 11 * 60, 12 * 60, 13.5 * 60, 16 * 60, 16.5 * 60]  # 9:30, 10:30, 11:00, 12:00, 13:30, 16:00, 16:30 in minutes
helen_constraints = [Not(And(meeting_start >= 9 * 60, meeting_start < 9.5 * 60)),
                     Not(And(meeting_start >= 10.5 * 60, meeting_start < 11 * 60)),
                     Not(And(meeting_start >= 12 * 60, meeting_start < 12.5 * 60)),
                     Not(And(meeting_start >= 13.5 * 60, meeting_start < 16 * 60)),
                     Not(meeting_end < 16 * 60),
                     Not(And(meeting_start >= 16.5 * 60, meeting_start <= 16.5 * 60 + 30)),
                     Not(meeting_end > 16.5 * 60 + 30)]

# Define the constraints for the meeting duration
duration_constraints = [meeting_end - meeting_start == meeting_duration]

# Define the solver
solver = Solver()

# Add the constraints to the solver
solver.add(And(christine_constraints, helen_constraints, duration_constraints))

# Check if a solution exists
if solver.check() == sat:
    # Get the solution
    model = solver.model()
    meeting_start_value = model[meeting_start].as_long()
    meeting_end_value = model[meeting_end].as_long()

    # Print the solution
    print(f"SOLUTION:")
    print(f"Day: {day}")
    print(f"Start Time: {meeting_start_value // 60:02d}:{meeting_start_value % 60:02d}")
    print(f"End Time: {meeting_end_value // 60:02d}:{meeting_end_value % 60:02d}")
else:
    print("No solution exists.")