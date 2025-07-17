from z3 import *

# Define the variables
day = Int('day')  # 0 for Monday, 1 for Tuesday, 2 for Wednesday
start_time = Int('start_time')  # in minutes from 9:00

# Define the constraints
constraints = []

# Meeting duration is 30 minutes
meeting_duration = 30

# Define the work hours in minutes from 9:00
work_start = 0
work_end = 480  # 17:00 - 9:00 = 8 hours = 480 minutes

# Define the blocked times for Nancy
nancy_blocked_times = [
    (60, 90),  # 10:00 to 10:30
    (150, 180),  # 11:30 to 12:30
    (270, 300),  # 13:30 to 14:00
    (330, 390),  # 14:30 to 15:30
    (420, 480)  # 16:00 to 17:00
]

# Define the blocked times for Jose
jose_blocked_times = [
    (0, 480),  # 9:00 to 17:00 on Monday
    (0, 480),  # 9:00 to 17:00 on Tuesday
    (0, 30),  # 9:00 to 9:30 on Wednesday
    (60, 150),  # 10:00 to 12:30 on Wednesday
    (270, 290),  # 13:30 to 14:30 on Wednesday
    (360, 480)  # 15:00 to 17:00 on Wednesday
]

# Constraints for the day
constraints.append(day >= 0)
constraints.append(day <= 2)

# Constraints for the start time
constraints.append(start_time >= work_start)
constraints.append(start_time + meeting_duration <= work_end)

# Constraints for Nancy's availability
for blocked_start, blocked_end in nancy_blocked_times:
    constraints.append(Or(start_time + meeting_duration <= blocked_start, start_time >= blocked_end))

# Constraints for Jose's availability
for blocked_start, blocked_end in jose_blocked_times:
    constraints.append(Or(start_time + meeting_duration <= blocked_start, start_time >= blocked_end))

# Add constraints for the specific days
constraints.append(Or(
    And(day == 0, start_time + meeting_duration <= 60),  # Monday, before 10:00
    And(day == 1, start_time + meeting_duration <= 90),  # Tuesday, before 10:30
    And(day == 2, start_time + meeting_duration <= 60)   # Wednesday, before 10:00
))

# Create the solver and add the constraints
solver = Solver()
solver.add(constraints)

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    meeting_day = model[day].as_long()
    meeting_start_time = model[start_time].as_long()
    meeting_end_time = meeting_start_time + meeting_duration

    # Convert the day and time to the required format
    days = ["Monday", "Tuesday", "Wednesday"]
    start_time_str = f"{9 + meeting_start_time // 60:02}:{meeting_start_time % 60:02}"
    end_time_str = f"{9 + meeting_end_time // 60:02}:{meeting_end_time % 60:02}"

    print(f"SOLUTION:\nDay: {days[meeting_day]}\nStart Time: {start_time_str}\nEnd Time: {end_time_str}")
else:
    print("No solution found")