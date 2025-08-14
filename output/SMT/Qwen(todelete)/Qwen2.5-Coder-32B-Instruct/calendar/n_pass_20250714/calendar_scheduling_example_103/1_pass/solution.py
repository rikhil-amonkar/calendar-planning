from z3 import *

# Define the time intervals as integers representing minutes since 9:00 AM
start_time = 9 * 60
end_time = 17 * 60
meeting_duration = 30

# Create a Z3 solver instance
solver = Solver()

# Define the meeting start time variable
meeting_start = Int('meeting_start')

# Add constraints for the meeting start time to be within working hours
solver.add(meeting_start >= start_time)
solver.add(meeting_start <= end_time - meeting_duration)

# Define the busy intervals for each participant
busy_intervals = {
    "Diane": [(9*60 + 30, 10*60), (14*60 + 30, 15*60)],
    "Jack": [(13*60 + 30, 14*60), (14*60 + 30, 15*60)],
    "Eugene": [(9*60, 10*60), (10*60 + 30, 11*60 + 30), (12*60, 14*60 + 30), (15*60, 16*60 + 30)],
    "Patricia": [(9*60 + 30, 10*60 + 30), (11*60, 12*60), (12*60 + 30, 14*60), (15*60, 16*60 + 30)]
}

# Add constraints to avoid busy intervals
for intervals in busy_intervals.values():
    for start, end in intervals:
        solver.add(Or(meeting_start + meeting_duration <= start, meeting_start >= end))

# Check if there is a feasible solution
if solver.check() == sat:
    model = solver.model()
    meeting_start_minutes = model[meeting_start].as_long()
    meeting_start_time = f"{(meeting_start_minutes // 60):02}:{(meeting_start_minutes % 60):02}"
    meeting_end_time = f"{((meeting_start_minutes + meeting_duration) // 60):02}:{((meeting_start_minutes + meeting_duration) % 60):02}"
    print(f"SOLUTION:\nDay: Monday\nStart Time: {meeting_start_time}\nEnd Time: {meeting_end_time}")
else:
    print("No feasible solution found.")