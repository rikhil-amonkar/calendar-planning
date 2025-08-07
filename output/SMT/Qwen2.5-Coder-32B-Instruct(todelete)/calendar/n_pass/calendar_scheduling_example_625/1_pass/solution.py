from z3 import *

# Define the variables
day = Int('day')  # 0 for Monday, 1 for Tuesday
start_time = Int('start_time')  # in minutes from 00:00

# Define the constraints
meeting_duration = 30  # 30 minutes

# Work hours are from 9:00 to 17:00 (540 to 1020 minutes from 00:00)
work_start = 540
work_end = 1020

# Jeffrey is free the entire week, so no additional constraints for him

# Harold's schedule
harold_busy_monday = Or(And(start_time >= 540, start_time < 600), And(start_time >= 630, start_time < 1020))
harold_busy_tuesday = Or(And(start_time >= 540, start_time < 570), And(start_time >= 630, start_time < 690),
                         And(start_time >= 750, start_time < 810), And(start_time >= 870, start_time < 930),
                         And(start_time >= 960, start_time < 1020))

# Harold's preference: avoid Monday and prefer Tuesday before 14:30 (870 minutes from 00:00)
harold_avoid_monday = day != 0
harold_prefer_tuesday_before_1430 = Or(day != 1, start_time < 870)

# Meeting must be within work hours
meeting_within_work_hours = And(start_time >= work_start, start_time + meeting_duration <= work_end)

# Meeting must not overlap with Harold's busy times
meeting_not_overlap_harold = Or(And(day == 0, Not(harold_busy_monday)),
                               And(day == 1, Not(harold_busy_tuesday)))

# Create the solver
solver = Solver()

# Add constraints to the solver
solver.add(meeting_within_work_hours)
solver.add(meeting_not_overlap_harold)
solver.add(harold_avoid_monday)
solver.add(harold_prefer_tuesday_before_1430)
solver.add(Or(day == 0, day == 1))  # day can only be Monday or Tuesday

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    meeting_day = "Monday" if model[day].as_long() == 0 else "Tuesday"
    meeting_start_time = model[start_time].as_long()
    meeting_start_time_formatted = f"{meeting_start_time // 60:02}:{meeting_start_time % 60:02}"
    meeting_end_time_formatted = f"{(meeting_start_time + meeting_duration) // 60:02}:{(meeting_start_time + meeting_duration) % 60:02}"
    print(f"SOLUTION:\nDay: {meeting_day}\nStart Time: {meeting_start_time_formatted}\nEnd Time: {meeting_end_time_formatted}")
else:
    print("No solution found")