from z3 import *

# Define the time slots as integers representing minutes since 9:00 AM
start_of_day = 9 * 60  # 9:00 AM
end_of_day = 17 * 60   # 17:00 PM

# Define the meeting duration in minutes
meeting_duration = 30  # 30 minutes

# Define the variables for the start time of the meeting
meeting_start = Int('meeting_start')

# Create a solver instance
solver = Solver()

# Constraints for Evelyn (no meetings all day)
# No additional constraints needed for Evelyn as she is free all day

# Constraints for Randy
# Randy's blocked times are: 9:00 to 10:30, 11:00 to 15:30, 16:00 to 17:00
blocked_times_randy = [
    (9 * 60, 10 * 60 + 30),  # 9:00 to 10:30
    (11 * 60, 15 * 60 + 30), # 11:00 to 15:30
    (16 * 60, 17 * 60)       # 16:00 to 17:00
]

# Add constraints to ensure the meeting does not overlap with Randy's blocked times
for start, end in blocked_times_randy:
    solver.add(Or(meeting_start + meeting_duration <= start, meeting_start >= end))

# Constraint for Evelyn's preference (do not meet after 13:00)
solver.add(meeting_start + meeting_duration <= 13 * 60)

# Constraint to ensure the meeting is within work hours
solver.add(meeting_start >= start_of_day)
solver.add(meeting_start + meeting_duration <= end_of_day)

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    meeting_start_minutes = model[meeting_start].as_long()
    meeting_start_time = f"{(meeting_start_minutes // 60):02}:{(meeting_start_minutes % 60):02}"
    meeting_end_time = f"{((meeting_start_minutes + meeting_duration) // 60):02}:{((meeting_start_minutes + meeting_duration) % 60):02}"
    print(f"SOLUTION:\nDay: Monday\nStart Time: {meeting_start_time}\nEnd Time: {meeting_end_time}")
else:
    print("No solution found")