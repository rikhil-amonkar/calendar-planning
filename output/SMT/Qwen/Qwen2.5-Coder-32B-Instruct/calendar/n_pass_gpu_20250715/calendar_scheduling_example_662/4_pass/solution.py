from z3 import *

# Define the variables
day = Int('day')  # 0 for Monday, 1 for Tuesday
start_time = Int('start_time')  # Start time in minutes from 9:00

# Constants for the time range in minutes from 9:00
nine_am = 0
five_pm = 480  # 17:00 - 9:00 = 8 hours * 60 minutes

# Meeting duration in minutes
meeting_duration = 60

# Define the constraints
constraints = []

# Constraints for Gary's availability
gary_unavailable_monday = Or(
    And(start_time >= 30, start_time < 60),  # 9:30 to 10:00
    And(start_time >= 60, start_time < 780),  # 11:00 to 13:00
    And(start_time >= 840, start_time < 870),  # 14:00 to 14:30
    And(start_time >= 990, start_time < 1020)  # 16:30 to 17:00
)

gary_unavailable_tuesday = Or(
    And(start_time >= 30, start_time < 60),  # 9:30 to 10:00
    And(start_time >= 630, start_time < 660)  # 10:30 to 11:00
)

# Constraints for David's availability
david_unavailable_monday = Or(
    And(start_time >= 30, start_time < 60),  # 9:30 to 10:00
    And(start_time >= 0, start_time < 780),  # 9:00 to 13:00
    And(start_time >= 870, start_time < 990)  # 14:30 to 16:30
)

david_unavailable_tuesday = Or(
    And(start_time >= 30, start_time < 60),  # 9:30 to 10:00
    And(start_time >= 60, start_time < 630),  # 10:00 to 10:30
    And(start_time >= 630, start_time < 750),  # 11:00 to 12:30
    And(start_time >= 780, start_time < 870),  # 13:00 to 14:30
    And(start_time >= 900, start_time < 960),  # 15:00 to 16:00
    And(start_time >= 990, start_time < 1020)  # 16:30 to 17:00
)

# Add constraints for both days
constraints.append(Or(day == 0, day == 1))  # Only Monday or Tuesday
constraints.append(start_time >= nine_am)
constraints.append(start_time + meeting_duration <= five_pm)

constraints.append(Implies(day == 0, Not(gary_unavailable_monday)))
constraints.append(Implies(day == 0, Not(david_unavailable_monday)))

constraints.append(Implies(day == 1, Not(gary_unavailable_tuesday)))
constraints.append(Implies(day == 1, Not(david_unavailable_tuesday)))

# Solve the constraints
solver = Solver()
solver.add(constraints)

if solver.check() == sat:
    model = solver.model()
    meeting_day = "Monday" if model[day].as_long() == 0 else "Tuesday"
    meeting_start_time = model[start_time].as_long()
    meeting_start_hour = meeting_start_time // 60 + 9
    meeting_start_minute = meeting_start_time % 60
    meeting_end_time = meeting_start_time + meeting_duration
    meeting_end_hour = meeting_end_time // 60 + 9
    meeting_end_minute = meeting_end_time % 60
    
    print(f"SOLUTION:\nDay: {meeting_day}\nStart Time: {meeting_start_hour:02}:{meeting_start_minute:02}\nEnd Time: {meeting_end_hour:02}:{meeting_end_minute:02}")
else:
    print("No solution found")