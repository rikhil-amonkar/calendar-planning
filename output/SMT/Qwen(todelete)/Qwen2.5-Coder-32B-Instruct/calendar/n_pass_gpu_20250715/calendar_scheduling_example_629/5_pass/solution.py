from z3 import *

# Define the variables
day = Int('day')  # 0 for Monday, 1 for Tuesday
start_time = Int('start_time')  # in minutes since 9:00

# Define the constants for the meeting duration
meeting_duration = 30  # 30 minutes

# Define the constraints
constraints = [
    Or(day == 0, day == 1),  # Day can only be Monday or Tuesday
    start_time >= 0,  # Start time must be after 9:00
    start_time + meeting_duration <= 480,  # End time must be before 17:00 (480 minutes after 9:00)
]

# Margaret's constraints
margaret_constraints = [
    Not(And(day == 0, start_time >= 60, start_time < 90)),  # Not 10:30 to 11:00
    Not(And(day == 0, start_time >= 90, start_time < 120)),  # Not 11:30 to 12:00
    Not(And(day == 0, start_time >= 180, start_time < 210)),  # Not 13:00 to 13:30
    Not(And(day == 0, start_time >= 300, start_time < 480)),  # Not 15:00 to 17:00
    Not(And(day == 1, start_time >= 60, start_time < 90)),  # Not 12:00 to 12:30
]

# Alexis's constraints
alexis_constraints = [
    Not(And(day == 0, start_time >= 30, start_time < 90)),  # Not 9:30 to 11:30
    Not(And(day == 0, start_time >= 150, start_time < 180)),  # Not 12:30 to 13:00
    Not(And(day == 0, start_time >= 240, start_time < 480)),  # Not 14:00 to 17:00
    Not(And(day == 1, start_time >= 0, start_time < 30)),  # Not 9:00 to 9:30
    Not(And(day == 1, start_time >= 30, start_time < 60)),  # Not 10:00 to 10:30
    Not(And(day == 1, start_time >= 240, start_time < 390)),  # Not 14:00 to 16:30
]

# Additional constraint: Margaret does not want to meet on Monday
margaret_additional_constraint = [
    Not(day == 0)
]

# Additional constraint: Meeting should be before 14:30 on Tuesday
tuesday_constraint = [
    Or(day == 0, start_time + meeting_duration <= 330)  # If Tuesday, meeting should end before 14:30 (330 minutes after 9:00)
]

# Combine all constraints
all_constraints = constraints + margaret_constraints + alexis_constraints + margaret_additional_constraint + tuesday_constraint

# Create the solver and add constraints
solver = Solver()
solver.add(all_constraints)

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    meeting_day = "Monday" if model[day].as_long() == 0 else "Tuesday"
    meeting_start_time_minutes = model[start_time].as_long()
    meeting_start_time = f"{9 + meeting_start_time_minutes // 60}:{meeting_start_time_minutes % 60:02}"
    meeting_end_time_minutes = meeting_start_time_minutes + meeting_duration
    meeting_end_time = f"{9 + meeting_end_time_minutes // 60}:{meeting_end_time_minutes % 60:02}"
    
    print(f"SOLUTION:\nDay: {meeting_day}\nStart Time: {meeting_start_time}\nEnd Time: {meeting_end_time}")
else:
    print("No solution found")