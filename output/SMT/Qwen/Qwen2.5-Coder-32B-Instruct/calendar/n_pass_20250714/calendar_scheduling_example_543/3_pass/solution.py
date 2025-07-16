from z3 import *

# Define the variables for the meeting start time
start_hour = Int('start_hour')
start_minute = Int('start_minute')

# Define the duration of the meeting
meeting_duration = 60  # 1 hour

# Define the work hours
work_start_hour = 9
work_end_hour = 17

# Define the constraints for James
james_busy_times = [(11, 30, 12, 0), (14, 30, 15, 0)]

# Define the constraints for John
john_busy_times = [(9, 30, 11, 0), (11, 30, 12, 0), (12, 30, 13, 30), (14, 30, 16, 30)]

# Create the solver
solver = Solver()

# Add constraints for the meeting to be within work hours
solver.add(start_hour >= work_start_hour)
solver.add(start_hour < work_end_hour)
solver.add(start_minute >= 0)
solver.add(start_minute < 60)

# Add constraints for the meeting to not overlap with James's busy times
for start_h, start_m, end_h, end_m in james_busy_times:
    solver.add(Or(start_hour * 60 + start_minute <= start_h * 60 + start_m,
                 start_hour * 60 + start_minute + meeting_duration >= end_h * 60 + end_m))

# Add constraints for the meeting to not overlap with John's busy times
for start_h, start_m, end_h, end_m in john_busy_times:
    solver.add(Or(start_hour * 60 + start_minute <= start_h * 60 + start_m,
                 start_hour * 60 + start_minute + meeting_duration >= end_h * 60 + end_m))

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    start_time_minutes = model[start_hour].as_long() * 60 + model[start_minute].as_long()
    start_time_hour = start_time_minutes // 60
    start_time_minute = start_time_minutes % 60
    end_time_minutes = start_time_minutes + meeting_duration
    end_time_hour = end_time_minutes // 60
    end_time_minute = end_time_minutes % 60
    print(f"SOLUTION:\nDay: Monday\nStart Time: {start_time_hour:02}:{start_time_minute:02}\nEnd Time: {end_time_hour:02}:{end_time_minute:02}")
else:
    print("No solution found")