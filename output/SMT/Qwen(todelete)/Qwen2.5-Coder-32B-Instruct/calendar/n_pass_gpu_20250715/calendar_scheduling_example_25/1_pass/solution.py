from z3 import *

# Define the variables for the meeting start time
meeting_start = Int('meeting_start')

# Constraints for the meeting duration
meeting_duration = 60  # One hour in minutes

# Convert times to minutes since the start of the day (9:00 AM)
def time_to_minutes(hour, minute):
    return (hour - 9) * 60 + minute

# Define the available time slots for each participant
anthony_busy = [
    (time_to_minutes(9, 30), time_to_minutes(10, 0)),
    (time_to_minutes(12, 0), time_to_minutes(13, 0)),
    (time_to_minutes(16, 0), time_to_minutes(16, 30))
]

pamela_busy = [
    (time_to_minutes(9, 30), time_to_minutes(10, 0)),
    (time_to_minutes(16, 30), time_to_minutes(17, 0))
]

zachary_busy = [
    (time_to_minutes(9, 0), time_to_minutes(11, 30)),
    (time_to_minutes(12, 0), time_to_minutes(12, 30)),
    (time_to_minutes(13, 0), time_to_minutes(13, 30)),
    (time_to_minutes(14, 30), time_to_minutes(15, 0)),
    (time_to_minutes(16, 0), time_to_minutes(17, 0))
]

# Define the total working hours in minutes
work_start = time_to_minutes(9, 0)
work_end = time_to_minutes(17, 0)

# Define Pamela's preference not to meet after 14:30
pamela_preference_end = time_to_minutes(14, 30)

# Create the solver
solver = Solver()

# Add constraints for the meeting start time
solver.add(meeting_start >= work_start)
solver.add(meeting_start + meeting_duration <= work_end)
solver.add(meeting_start + meeting_duration <= pamela_preference_end)

# Add constraints to avoid busy times for each participant
for start, end in anthony_busy:
    solver.add(Or(meeting_start + meeting_duration <= start, meeting_start >= end))

for start, end in pamela_busy:
    solver.add(Or(meeting_start + meeting_duration <= start, meeting_start >= end))

for start, end in zachary_busy:
    solver.add(Or(meeting_start + meeting_duration <= start, meeting_start >= end))

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    meeting_start_minutes = model[meeting_start].as_long()
    meeting_start_hour = meeting_start_minutes // 60 + 9
    meeting_start_minute = meeting_start_minutes % 60
    meeting_end_minutes = meeting_start_minutes + meeting_duration
    meeting_end_hour = meeting_end_minutes // 60 + 9
    meeting_end_minute = meeting_end_minutes % 60
    
    print("SOLUTION:")
    print(f"Day: Monday")
    print(f"Start Time: {meeting_start_hour:02}:{meeting_start_minute:02}")
    print(f"End Time: {meeting_end_hour:02}:{meeting_end_minute:02}")
else:
    print("No solution found")