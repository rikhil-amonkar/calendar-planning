from z3 import *

# Define variables
day = Int('day')  # Day of the week: 0=Monday, 1=Tuesday, 2=Wednesday, 3=Thursday, 4=Friday
start_time = Int('start_time')  # Start time in minutes from 9:00

# Define constants for the days
MONDAY, TUESDAY, WEDNESDAY, THURSDAY, FRIDAY = 0, 1, 2, 3, 4

# Define the meeting duration
meeting_duration = 60  # 1 hour

# Define the work hours in minutes from 9:00
work_start = 0
work_end = 480  # 17:00 - 9:00 = 8 hours * 60 minutes/hour = 480 minutes

# Define the constraints for each participant
bryan_constraints = [
    Or(day != THURSDAY, Or(start_time < 540, start_time >= 750)),  # 9:30 to 10:00 and 12:30 to 13:00
    Or(day != FRIDAY, Or(start_time < 630, start_time >= 870))   # 10:30 to 11:00 and 14:00 to 14:30
]

nicholas_constraints = [
    Or(day != MONDAY, Or(start_time < 690, start_time >= 810)),  # 11:30 to 12:00 and 13:00 to 15:30
    Or(day != TUESDAY, Or(start_time < 540, start_time >= 570)),  # 9:00 to 9:30
    Or(day != TUESDAY, Or(start_time < 660, start_time >= 810)),  # 11:00 to 13:30
    Or(day != TUESDAY, Or(start_time < 840, start_time >= 990)),  # 14:00 to 16:30
    Or(day != WEDNESDAY, Or(start_time < 540, start_time >= 570)),  # 9:00 to 9:30
    Or(day != WEDNESDAY, Or(start_time < 600, start_time >= 660)),  # 10:00 to 11:00
    Or(day != WEDNESDAY, Or(start_time < 690, start_time >= 810)),  # 11:30 to 13:30
    Or(day != WEDNESDAY, Or(start_time < 840, start_time >= 870)),  # 14:00 to 14:30
    Or(day != WEDNESDAY, Or(start_time < 900, start_time >= 990)),  # 15:00 to 16:30
    Or(day != THURSDAY, Or(start_time < 630, start_time >= 690)),  # 10:30 to 11:30
    Or(day != THURSDAY, Or(start_time < 720, start_time >= 750)),  # 12:00 to 12:30
    Or(day != THURSDAY, Or(start_time < 900, start_time >= 930)),  # 15:00 to 15:30
    Or(day != THURSDAY, Or(start_time < 990, start_time >= 1020)),  # 16:30 to 17:00
    Or(day != FRIDAY, Or(start_time < 540, start_time >= 630)),  # 9:00 to 10:30
    Or(day != FRIDAY, Or(start_time < 660, start_time >= 720)),  # 11:00 to 12:00
    Or(day != FRIDAY, Or(start_time < 750, start_time >= 870)),  # 12:30 to 14:30
    Or(day != FRIDAY, Or(start_time < 930, start_time >= 990)),  # 15:30 to 16:00
    Or(day != FRIDAY, Or(start_time < 990, start_time >= 1020))   # 16:30 to 17:00
]

# Bryan's preference: avoid Tuesday
bryan_avoid_tuesday = day != TUESDAY

# Nicholas's preference: avoid Monday and Thursday
nicholas_avoid_monday_thursday = And(day != MONDAY, day != THURSDAY)

# Combine all constraints
constraints = [
    day >= 0, day <= 4,  # Valid day range
    start_time >= work_start, start_time + meeting_duration <= work_end,  # Within work hours
    bryan_avoid_tuesday,
    nicholas_avoid_monday_thursday
] + bryan_constraints + nicholas_constraints

# Create solver and add constraints
solver = Solver()
solver.add(constraints)

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    meeting_day = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"][model[day].as_long()]
    meeting_start_time = model[start_time].as_long()
    meeting_end_time = meeting_start_time + meeting_duration
    
    # Convert times to HH:MM format
    start_hour = 9 + meeting_start_time // 60
    start_minute = meeting_start_time % 60
    end_hour = 9 + meeting_end_time // 60
    end_minute = meeting_end_time % 60
    
    print(f"SOLUTION:")
    print(f"Day: {meeting_day}")
    print(f"Start Time: {start_hour:02}:{start_minute:02}")
    print(f"End Time: {end_hour:02}:{end_minute:02}")
else:
    print("No solution found")