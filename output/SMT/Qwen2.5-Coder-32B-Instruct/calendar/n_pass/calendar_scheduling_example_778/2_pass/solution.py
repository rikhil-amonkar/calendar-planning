from z3 import *

# Define the variables for the day and time
day = Int('day')  # 0 = Monday, 1 = Tuesday, 2 = Wednesday
start_time = Int('start_time')  # in minutes from 9:00

# Define the constraints
constraints = []

# Meeting duration is 30 minutes
meeting_duration = 30

# Define the work hours in minutes from 9:00
work_start = 0  # 9:00
work_end = 480  # 17:00

# Define the blocked times for Susan and Sandra
susan_blocked_times = [
    (180, 210),  # Monday 12:30 to 13:00
    (210, 240),  # Monday 13:30 to 14:00
    (390, 420),  # Tuesday 11:30 to 12:00
    (0, 60),     # Wednesday 9:30 to 10:30
    (360, 390),  # Wednesday 14:00 to 14:30
    (420, 480)   # Wednesday 15:30 to 16:30
]

sandra_blocked_times = [
    (0, 360),    # Monday 9:00 to 13:00
    (420, 480),  # Monday 14:00 to 15:00
    (540, 570),  # Monday 16:00 to 16:30
    (0, 30),     # Tuesday 9:00 to 9:30
    (60, 120),   # Tuesday 10:30 to 12:00
    (180, 210),  # Tuesday 12:30 to 13:30
    (240, 270),  # Tuesday 14:00 to 14:30
    (360, 480),  # Tuesday 16:00 to 17:00
    (0, 720),    # Wednesday 9:00 to 11:30
    (120, 150),  # Wednesday 12:00 to 12:30
    (180, 480)   # Wednesday 13:00 to 17:00
]

# Constraints for Susan and Sandra
for blocked_start, blocked_end in susan_blocked_times:
    constraints.append(Or(day != 0, Or(start_time + meeting_duration <= blocked_start, start_time >= blocked_end)))

for blocked_start, blocked_end in sandra_blocked_times:
    constraints.append(Or(day != 0, Or(start_time + meeting_duration <= blocked_start, start_time >= blocked_end)))

# Susan would rather not meet on Tuesday
constraints.append(day != 1)

# Sandra can not meet on Monday after 16:00
constraints.append(Or(day != 0, start_time + meeting_duration <= 360))

# Meeting must be within work hours
constraints.append(And(start_time >= work_start, start_time + meeting_duration <= work_end))

# Day must be Monday, Tuesday, or Wednesday
constraints.append(And(day >= 0, day <= 2))

# Create the solver and add the constraints
solver = Solver()
solver.add(constraints)

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    meeting_day = model[day].as_long()
    meeting_start_time = model[start_time].as_long()
    meeting_end_time = meeting_start_time + meeting_duration

    # Convert the day and time to human-readable format
    days = ["Monday", "Tuesday", "Wednesday"]
    start_time_str = f"{9 + meeting_start_time // 60:02}:{meeting_start_time % 60:02}"
    end_time_str = f"{9 + meeting_end_time // 60:02}:{meeting_end_time % 60:02}"

    print(f"SOLUTION:\nDay: {days[meeting_day]}\nStart Time: {start_time_str}\nEnd Time: {end_time_str}")
else:
    print("No solution found")