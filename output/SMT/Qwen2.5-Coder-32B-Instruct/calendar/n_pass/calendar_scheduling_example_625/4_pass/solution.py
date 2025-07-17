from z3 import *

# Define the variables
day = Int('day')  # 0 for Monday, 1 for Tuesday
start_time = Int('start_time')  # in minutes from 00:00

# Define the constraints
# Work hours are from 9:00 to 17:00 (540 to 1020 minutes from 00:00)
work_start = 540
work_end = 1020
meeting_duration = 30  # 30 minutes

# Jeffrey is free the entire week, so no additional constraints for him

# Harold's schedule
harold_busy_monday = Or(And(start_time >= 540, start_time < 600),  # 9:00 to 10:00
                         And(start_time >= 630, start_time < 1020))  # 10:30 to 17:00
harold_busy_tuesday = Or(And(start_time >= 540, start_time < 570),  # 9:00 to 9:30
                          And(start_time >= 630, start_time < 690),  # 10:30 to 11:30
                          And(start_time >= 750, start_time < 810),  # 12:30 to 13:30
                          And(start_time >= 870, start_time < 930),  # 14:30 to 15:30
                          And(start_time >= 960, start_time < 1020))  # 16:00 to 17:00

# Harold's preference: avoid Monday and prefer times after 14:30 on Tuesday
harold_avoid_monday = day != 0
harold_prefer_tuesday_after_1430 = Or(day != 1, start_time >= 870)  # 14:30 in minutes

# Meeting must be within work hours
meeting_within_work_hours = And(start_time >= work_start, start_time + meeting_duration <= work_end)

# Harold's availability
harold_available = And(If(day == 0, Not(harold_busy_monday), True),
                       If(day == 1, Not(harold_busy_tuesday), True))

# Create the solver
solver = Solver()

# Add constraints to the solver
solver.add(meeting_within_work_hours)
solver.add(harold_available)
solver.add(harold_avoid_monday)
solver.add(harold_prefer_tuesday_after_1430)

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    meeting_day = "Monday" if model[day].as_long() == 0 else "Tuesday"
    meeting_start_time = model[start_time].as_long()
    meeting_start_hour = meeting_start_time // 60
    meeting_start_minute = meeting_start_time % 60
    meeting_end_time = meeting_start_time + meeting_duration
    meeting_end_hour = meeting_end_time // 60
    meeting_end_minute = meeting_end_time % 60
    print(f"SOLUTION:\nDay: {meeting_day}\nStart Time: {meeting_start_hour:02}:{meeting_start_minute:02}\nEnd Time: {meeting_end_hour:02}:{meeting_end_minute:02}")
else:
    print("No solution found")