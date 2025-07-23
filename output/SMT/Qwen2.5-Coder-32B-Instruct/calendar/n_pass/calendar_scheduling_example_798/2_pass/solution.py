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
    (150, 210),  # 11:30 to 12:30
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
# Monday
constraints.append(Or(day != 0, And(
    Or(start_time + meeting_duration <= 60, start_time >= 90),  # 10:00 to 10:30
    Or(start_time + meeting_duration <= 150, start_time >= 210),  # 11:30 to 12:30
    Or(start_time + meeting_duration <= 270, start_time >= 300),  # 13:30 to 14:00
    Or(start_time + meeting_duration <= 330, start_time >= 390),  # 14:30 to 15:30
    Or(start_time + meeting_duration <= 420, start_time >= 480)  # 16:00 to 17:00
)))

# Tuesday
constraints.append(Or(day != 1, And(
    Or(start_time + meeting_duration <= 60, start_time >= 90),  # 9:30 to 10:30
    Or(start_time + meeting_duration <= 150, start_time >= 180),  # 11:00 to 11:30
    Or(start_time + meeting_duration <= 240, start_time >= 270),  # 12:00 to 12:30
    Or(start_time + meeting_duration <= 330, start_time >= 360),  # 13:00 to 13:30
    Or(start_time + meeting_duration <= 480, start_time >= 540)  # 15:30 to 16:00
)))

# Wednesday
constraints.append(Or(day != 2, And(
    Or(start_time + meeting_duration <= 30, start_time >= 60),  # 9:00 to 9:30
    Or(start_time + meeting_duration <= 150, start_time >= 210),  # 10:00 to 12:30
    Or(start_time + meeting_duration <= 270, start_time >= 290),  # 13:30 to 14:30
    Or(start_time + meeting_duration <= 360, start_time >= 480)  # 15:00 to 17:00
)))

# Solve the constraints
solver = Solver()
solver.add(constraints)

if solver.check() == sat:
    model = solver.model()
    day_value = model[day].as_long()
    start_time_value = model[start_time].as_long()
    end_time_value = start_time_value + meeting_duration

    # Convert day and time to human-readable format
    days = ["Monday", "Tuesday", "Wednesday"]
    start_time_str = f"{9 + start_time_value // 60}:{start_time_value % 60:02}"
    end_time_str = f"{9 + end_time_value // 60}:{end_time_value % 60:02}"

    print(f"SOLUTION:\nDay: {days[day_value]}\nStart Time: {start_time_str}\nEnd Time: {end_time_str}")
else:
    print("No solution found")