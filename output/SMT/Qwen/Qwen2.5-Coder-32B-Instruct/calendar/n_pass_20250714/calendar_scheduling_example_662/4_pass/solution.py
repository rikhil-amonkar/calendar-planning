from z3 import *

# Define the variables
day = Int('day')  # 0 for Monday, 1 for Tuesday
start_time = Int('start_time')  # in minutes from 9:00

# Define the constraints
solver = Solver()

# Meeting duration is 1 hour (60 minutes)
meeting_duration = 60

# Work hours are from 9:00 to 17:00, which is 480 minutes from 9:00
work_start = 0  # 9:00
work_end = 480  # 17:00

# Gary's availability
gary_unavailable_monday = [(30, 60), (60, 120), (120, 150), (390, 480)]
gary_unavailable_tuesday = [(0, 30), (60, 90), (270, 360)]

# David's availability
david_unavailable_monday = [(0, 30), (30, 180), (180, 240)]
david_unavailable_tuesday = [(0, 30), (30, 60), (60, 75), (120, 180), (150, 180), (390, 480)]

# Constraints for the day
solver.add(Or(day == 0, day == 1))

# Constraints for the start time
solver.add(start_time >= work_start)
solver.add(start_time + meeting_duration <= work_end)

# Constraints for Gary's availability on Monday
for unavailable_start, unavailable_end in gary_unavailable_monday:
    solver.add(Or(day != 0, Or(start_time + meeting_duration <= unavailable_start, start_time >= unavailable_end)))

# Constraints for David's availability on Monday
for unavailable_start, unavailable_end in david_unavailable_monday:
    solver.add(Or(day != 0, Or(start_time + meeting_duration <= unavailable_start, start_time >= unavailable_end)))

# Constraints for Gary's availability on Tuesday
for unavailable_start, unavailable_end in gary_unavailable_tuesday:
    solver.add(Or(day != 1, Or(start_time + meeting_duration <= unavailable_start, start_time >= unavailable_end)))

# Constraints for David's availability on Tuesday
for unavailable_start, unavailable_end in david_unavailable_tuesday:
    solver.add(Or(day != 1, Or(start_time + meeting_duration <= unavailable_start, start_time >= unavailable_end)))

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    meeting_day = "Monday" if model[day].as_long() == 0 else "Tuesday"
    meeting_start_time = model[start_time].as_long() + 9 * 60  # Convert back to time from 9:00
    meeting_start_hour = meeting_start_time // 60
    meeting_start_minute = meeting_start_time % 60
    meeting_end_time = meeting_start_time + meeting_duration
    meeting_end_hour = meeting_end_time // 60
    meeting_end_minute = meeting_end_time % 60
    
    print(f"SOLUTION:")
    print(f"Day: {meeting_day}")
    print(f"Start Time: {meeting_start_hour:02}:{meeting_start_minute:02}")
    print(f"End Time: {meeting_end_hour:02}:{meeting_end_minute:02}")
else:
    print("No solution found")