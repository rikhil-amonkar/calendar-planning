from z3 import *

# Define the variables for the meeting start time in minutes since 9:00 AM
meeting_start = Int('meeting_start')
meeting_duration = 30  # Meeting duration is 30 minutes

# Define the constraints for each person
constraints = []

# Joan: 11:30 to 12:00, 14:30 to 15:00
constraints.append(Or(meeting_start + meeting_duration <= 150, meeting_start >= 870))
constraints.append(Or(meeting_start + meeting_duration <= 870, meeting_start >= 900))

# Megan: 9:00 to 10:00, 14:00 to 14:30, 16:00 to 16:30
constraints.append(meeting_start + meeting_duration <= 60)
constraints.append(Or(meeting_start + meeting_duration <= 840, meeting_start >= 870))
constraints.append(Or(meeting_start + meeting_duration <= 960, meeting_start >= 990))

# Austin: Free all day
# No constraints needed for Austin

# Betty: 9:30 to 10:00, 11:30 to 12:00, 13:30 to 14:00, 16:00 to 16:30
constraints.append(Or(meeting_start + meeting_duration <= 60, meeting_start >= 90))
constraints.append(Or(meeting_start + meeting_duration <= 750, meeting_start >= 780))
constraints.append(Or(meeting_start + meeting_duration <= 810, meeting_start >= 840))
constraints.append(Or(meeting_start + meeting_duration <= 960, meeting_start >= 990))

# Judith: 9:00 to 11:00, 12:00 to 13:00, 14:00 to 15:00
constraints.append(Or(meeting_start + meeting_duration <= 120, meeting_start >= 720))
constraints.append(Or(meeting_start + meeting_duration <= 720, meeting_start >= 780))
constraints.append(Or(meeting_start + meeting_duration <= 840, meeting_start >= 900))

# Terry: 9:30 to 10:00, 11:30 to 12:30, 13:00 to 14:00, 15:00 to 15:30, 16:00 to 17:00
constraints.append(Or(meeting_start + meeting_duration <= 60, meeting_start >= 90))
constraints.append(Or(meeting_start + meeting_duration <= 750, meeting_start >= 780))
constraints.append(Or(meeting_start + meeting_duration <= 810, meeting_start >= 840))
constraints.append(Or(meeting_start + meeting_duration <= 900, meeting_start >= 930))
constraints.append(Or(meeting_start + meeting_duration <= 960, meeting_start >= 1020))

# Kathryn: 9:30 to 10:00, 10:30 to 11:00, 11:30 to 13:00, 14:00 to 16:00, 16:30 to 17:00
constraints.append(Or(meeting_start + meeting_duration <= 60, meeting_start >= 90))
constraints.append(Or(meeting_start + meeting_duration <= 90, meeting_start >= 120))
constraints.append(Or(meeting_start + meeting_duration <= 750, meeting_start >= 780))
constraints.append(Or(meeting_start + meeting_duration <= 840, meeting_start >= 960))
constraints.append(Or(meeting_start + meeting_duration <= 990, meeting_start >= 1020))

# Define the solver
solver = Solver()
solver.add(constraints)

# Add constraint that the meeting must be within working hours (9:00 to 17:00)
solver.add(meeting_start >= 0)
solver.add(meeting_start + meeting_duration <= 480)  # 480 minutes is 16:00 (17:00 - 9:00)

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    start_time_minutes = model[meeting_start].as_long()
    start_hour = 9 + start_time_minutes // 60
    start_minute = start_time_minutes % 60
    end_time_minutes = start_time_minutes + meeting_duration
    end_hour = 9 + end_time_minutes // 60
    end_minute = end_time_minutes % 60
    
    print(f"SOLUTION:\nDay: Monday\nStart Time: {start_hour:02}:{start_minute:02}\nEnd Time: {end_hour:02}:{end_minute:02}")
else:
    print("No solution found")