from z3 import *

# Define the time slots in minutes from 9:00 to 17:00
start_time = 9 * 60  # 9:00 in minutes
end_time = 17 * 60   # 17:00 in minutes
meeting_duration = 30  # 30 minutes

# Define the variables for the meeting start time
meeting_start = Int('meeting_start')

# Create a solver instance
solver = Solver()

# Add constraints for the meeting time to be within the work hours
solver.add(meeting_start >= start_time)
solver.add(meeting_start + meeting_duration <= end_time)

# Define the busy times for each participant
busy_times = {
    'Joe': [(9*60 + 30, 10*60), (10*60 + 30, 11*60)],
    'Keith': [(11*60 + 30, 12*60), (15*60, 15*60 + 30)],
    'Patricia': [(9*60, 9*60 + 30), (13*60, 13*60 + 30)],
    'Nancy': [(9*60, 11*60), (11*60 + 30, 16*60 + 30)],
    'Pamela': [(9*60, 10*60), (10*60 + 30, 11*60), (11*60 + 30, 12*60 + 30),
               (13*60, 14*60), (14*60 + 30, 15*60), (15*60 + 30, 16*60), (16*60 + 30, 17*60)]
}

# Add constraints to avoid busy times
for person, times in busy_times.items():
    for start, end in times:
        solver.add(Or(meeting_start + meeting_duration <= start, meeting_start >= end))

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    meeting_start_minutes = model[meeting_start].as_long()
    meeting_start_time = f"{meeting_start_minutes // 60:02}:{meeting_start_minutes % 60:02}"
    meeting_end_time = f"{(meeting_start_minutes + meeting_duration) // 60:02}:{(meeting_start_minutes + meeting_duration) % 60:02}"
    print(f"SOLUTION:\nDay: Monday\nStart Time: {meeting_start_time}\nEnd Time: {meeting_end_time}")
else:
    print("No solution found")