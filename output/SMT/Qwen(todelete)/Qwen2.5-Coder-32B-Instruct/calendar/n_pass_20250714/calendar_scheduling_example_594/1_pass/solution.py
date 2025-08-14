from z3 import *

# Define the time intervals in minutes since the start of the workday (9:00 AM)
work_start = 9 * 60  # 9:00 AM
work_end = 17 * 60   # 5:00 PM
meeting_duration = 30  # 30 minutes

# Define the busy times for Adam and Roy in minutes since the start of the workday
adam_busy_times = [(9.5 * 60, 10 * 60), (12.5 * 60, 13 * 60), (14.5 * 60, 15 * 60), (16.5 * 60, 17 * 60)]
roy_busy_times = [(10 * 60, 11 * 60), (11.5 * 60, 13 * 60), (13.5 * 60, 14.5 * 60), (16.5 * 60, 17 * 60)]

# Create a solver instance
solver = Solver()

# Define a variable for the start time of the meeting
start_time = Int('start_time')

# Add constraints that the meeting must be within work hours
solver.add(start_time >= work_start)
solver.add(start_time + meeting_duration <= work_end)

# Add constraints that the meeting does not overlap with any busy times
for busy_start, busy_end in adam_busy_times:
    solver.add(Or(start_time + meeting_duration <= busy_start, start_time >= busy_end))

for busy_start, busy_end in roy_busy_times:
    solver.add(Or(start_time + meeting_duration <= busy_start, start_time >= busy_end))

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    meeting_start = model[start_time].as_long()
    meeting_end = meeting_start + meeting_duration
    
    # Convert the meeting start and end times back to HH:MM format
    def format_time(minutes):
        hours = minutes // 60
        minutes = minutes % 60
        return f"{hours:02}:{minutes:02}"
    
    meeting_start_formatted = format_time(meeting_start)
    meeting_end_formatted = format_time(meeting_end)
    
    print("SOLUTION:")
    print(f"Day: Monday")
    print(f"Start Time: {meeting_start_formatted}")
    print(f"End Time: {meeting_end_formatted}")
else:
    print("No solution found")