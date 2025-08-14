from z3 import *

# Define the time slots in minutes from 9:00 to 17:00
start_time = 9 * 60  # 9:00 in minutes
end_time = 17 * 60   # 17:00 in minutes
meeting_duration = 30  # Meeting duration in minutes

# Create a solver instance
solver = Solver()

# Define a variable for the start time of the meeting
meeting_start = Int('meeting_start')

# Add constraints for the meeting start time
solver.add(meeting_start >= start_time)
solver.add(meeting_start <= end_time - meeting_duration)

# Define the busy times for each participant
busy_times = {
    'Eric': [],
    'Ashley': [(10 * 60, 10 * 60 + 30), (11 * 60, 12 * 60), (12 * 60 + 30, 13 * 60), (15 * 60, 16 * 60)],
    'Ronald': [(9 * 60, 9 * 60 + 30), (10 * 60, 11 * 60 + 30), (12 * 60 + 30, 14 * 60), (14 * 60 + 30, 17 * 60)],
    'Larry': [(9 * 60, 12 * 60), (13 * 60, 17 * 60)]
}

# Add constraints to avoid busy times
for person, times in busy_times.items():
    for start, end in times:
        solver.add(Or(meeting_start + meeting_duration <= start, meeting_start >= end))

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    meeting_start_minutes = model[meeting_start].as_long()
    meeting_start_hour = meeting_start_minutes // 60
    meeting_start_minute = meeting_start_minutes % 60
    meeting_end_minutes = meeting_start_minutes + meeting_duration
    meeting_end_hour = meeting_end_minutes // 60
    meeting_end_minute = meeting_end_minutes % 60
    
    print("SOLUTION:")
    print(f"Day: Monday")
    print(f"Start Time: {meeting_start_hour:02}:{meeting_start_minute:02}")
    print(f"End Time: {meeting_end_hour:02}:{meeting_end_minute:02}")
else:
    print("No solution found.")