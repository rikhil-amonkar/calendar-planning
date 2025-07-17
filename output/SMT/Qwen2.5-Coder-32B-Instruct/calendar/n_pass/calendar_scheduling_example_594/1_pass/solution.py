from z3 import *

# Define the time variables
day = Int('day')
start_time = Int('start_time')
end_time = Int('end_time')

# Define the constraints
solver = Solver()

# Meeting duration is 30 minutes
meeting_duration = 30

# Work hours are from 9:00 to 17:00 (9 to 17 in 24-hour format)
work_start = 9 * 60  # 9:00 in minutes
work_end = 17 * 60   # 17:00 in minutes

# Convert busy times to minutes for easier calculation
adam_busy_times = [(9*60 + 30, 10*60), (12*60 + 30, 13*60), (14*60 + 30, 15*60), (16*60 + 30, 17*60)]
roy_busy_times = [(10*60, 11*60), (11*60 + 30, 13*60), (13*60 + 30, 14*60 + 30), (16*60 + 30, 17*60)]

# Constraints for the meeting
solver.add(day == 1)  # Monday
solver.add(start_time >= work_start)
solver.add(end_time <= work_end)
solver.add(end_time == start_time + meeting_duration)

# Adam's busy times
for busy_start, busy_end in adam_busy_times:
    solver.add(Or(end_time <= busy_start, start_time >= busy_end))

# Roy's busy times
for busy_start, busy_end in roy_busy_times:
    solver.add(Or(end_time <= busy_start, start_time >= busy_end))

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    meeting_day = model[day].as_long()
    meeting_start = model[start_time].as_long()
    meeting_end = model[end_time].as_long()
    
    # Convert meeting start and end times back to HH:MM format
    start_hour = meeting_start // 60
    start_minute = meeting_start % 60
    end_hour = meeting_end // 60
    end_minute = meeting_end % 60
    
    print(f"SOLUTION:")
    print(f"Day: Monday")
    print(f"Start Time: {start_hour:02}:{start_minute:02}")
    print(f"End Time: {end_hour:02}:{end_minute:02}")
else:
    print("No solution found")