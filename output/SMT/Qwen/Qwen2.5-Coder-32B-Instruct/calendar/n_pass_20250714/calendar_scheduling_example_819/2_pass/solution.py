from z3 import *

# Define the variables
day = Int('day')  # Monday=0, Tuesday=1, Wednesday=2, Thursday=3
start_time = Int('start_time')  # in minutes since 9:00

# Define the constraints
constraints = []

# Constraints for valid day
constraints.append(day >= 0)
constraints.append(day <= 3)

# Constraints for valid start time (9:00 to 16:30, in minutes)
constraints.append(start_time >= 0)
constraints.append(start_time + 30 <= 540)  # 540 minutes is 9:00 + 9 hours

# Ruth's availability
# Ruth is available on Thursday from 11:30 to 15:00
# Convert times to minutes since 9:00
ruth_start = 150  # 11:30 in minutes since 9:00
ruth_end = 360    # 15:00 in minutes since 9:00

# Ruth is not available on Monday, Tuesday, Wednesday, Thursday before 11:30 and after 15:00
constraints.append(Or(day != 0, start_time >= 540))  # Not available on Monday
constraints.append(Or(day != 1, start_time >= 540))  # Not available on Tuesday
constraints.append(Or(day != 2, start_time >= 540))  # Not available on Wednesday
constraints.append(Or(day != 3, Or(start_time >= ruth_start, start_time + 30 <= ruth_end)))

# Julie's preference: avoid meetings on Thursday before 11:30
julie_avoid_start = 150  # 11:30 in minutes since 9:00
constraints.append(Or(day != 3, start_time >= julie_avoid_start))

# Solve the constraints
solver = Solver()
solver.add(constraints)

if solver.check() == sat:
    model = solver.model()
    meeting_day = ["Monday", "Tuesday", "Wednesday", "Thursday"][model[day].as_long()]
    meeting_start_time_minutes = model[start_time].as_long()
    meeting_start_time = f"{9 + meeting_start_time_minutes // 60}:{meeting_start_time_minutes % 60:02d}"
    meeting_end_time = f"{9 + (meeting_start_time_minutes + 30) // 60}:{(meeting_start_time_minutes + 30) % 60:02d}"
    
    print(f"SOLUTION:\nDay: {meeting_day}\nStart Time: {meeting_start_time}\nEnd Time: {meeting_end_time}")
else:
    print("No solution found")