from z3 import *

# Define the variables
day = Int('day')  # 0 for Monday, 1 for Tuesday
start_time = Int('start_time')  # in minutes from 9:00

# Define the constraints
constraints = []

# Meeting duration is 30 minutes
meeting_duration = 30

# Working hours are from 9:00 to 17:00, which is 480 minutes from 9:00
working_hours_start = 0  # 9:00
working_hours_end = 480  # 17:00

# Constraints for Margaret's availability
constraints.append(Or(day == 1, Or(start_time < 630, And(start_time >= 690, start_time < 780), And(start_time >= 810, start_time < 840))))
constraints.append(Or(day == 1, start_time < 900))

# Constraints for Alexis's availability
constraints.append(Or(day == 1, Or(start_time < 240, And(start_time >= 780, start_time < 840), And(start_time >= 870, start_time < 1020))))
constraints.append(Or(day == 0, Or(start_time < 60, And(start_time >= 360, start_time < 630), And(start_time >= 840, start_time < 990))))

# Margaret does not want to meet on Monday
constraints.append(day == 1)

# Meeting must be within working hours
constraints.append(start_time >= working_hours_start)
constraints.append(start_time + meeting_duration <= working_hours_end)

# Additional constraint for Alexis's unavailability on Tuesday from 14:00 to 16:30
constraints.append(Or(day == 0, Or(start_time < 300, start_time >= 390)))

# Ensure the meeting does not overlap with Alexis's unavailability on Tuesday from 14:00 to 16:30
constraints.append(Or(day == 0, Or(start_time + meeting_duration <= 300, start_time >= 390)))

# Ensure the meeting does not overlap with Alexis's unavailability on Tuesday from 9:00 to 9:30
constraints.append(Or(day == 0, Or(start_time < 30, start_time >= 60)))

# Create the solver and add constraints
solver = Solver()
solver.add(constraints)

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    meeting_day = "Monday" if model[day].as_long() == 0 else "Tuesday"
    meeting_start_time = model[start_time].as_long() + 540  # Convert minutes from 9:00 to actual time
    meeting_start_hour = meeting_start_time // 60
    meeting_start_minute = meeting_start_time % 60
    meeting_end_time = meeting_start_time + meeting_duration
    meeting_end_hour = meeting_end_time // 60
    meeting_end_minute = meeting_end_time % 60
    print(f"SOLUTION:\nDay: {meeting_day}\nStart Time: {meeting_start_hour:02}:{meeting_start_minute:02}\nEnd Time: {meeting_end_hour:02}:{meeting_end_minute:02}")
else:
    print("No solution found")