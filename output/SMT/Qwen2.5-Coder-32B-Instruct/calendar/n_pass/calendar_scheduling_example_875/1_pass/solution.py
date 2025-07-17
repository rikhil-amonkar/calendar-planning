from z3 import *

# Define the variables
day = Int('day')  # 0 = Monday, 1 = Tuesday, 2 = Wednesday, 3 = Thursday
start_time = Int('start_time')  # in minutes from 9:00

# Define the constraints
solver = Solver()

# Meeting duration is 1 hour (60 minutes)
meeting_duration = 60

# Define the work hours
work_start = 9 * 60  # 9:00 in minutes
work_end = 17 * 60  # 17:00 in minutes

# Define the days
solver.add(day >= 0)
solver.add(day <= 3)

# Define the start time within work hours
solver.add(start_time >= work_start)
solver.add(start_time + meeting_duration <= work_end)

# Define Natalie's busy times
natalie_busy_times = [
    (0, 9 * 60, 9 * 60 + 30),  # Monday 9:00 to 9:30
    (0, 10 * 60, 12 * 60),     # Monday 10:00 to 12:00
    (0, 12 * 60 + 30, 13 * 60),# Monday 12:30 to 13:00
    (0, 14 * 60, 14 * 60 + 30),# Monday 14:00 to 14:30
    (0, 15 * 60, 16 * 60 + 30),# Monday 15:00 to 16:30
    (1, 9 * 60, 9 * 60 + 30),  # Tuesday 9:00 to 9:30
    (1, 10 * 60, 10 * 60 + 30),# Tuesday 10:00 to 10:30
    (1, 12 * 60 + 30, 14 * 60),# Tuesday 12:30 to 14:00
    (1, 16 * 60, 17 * 60),     # Tuesday 16:00 to 17:00
    (2, 11 * 60, 11 * 60 + 30),# Wednesday 11:00 to 11:30
    (2, 16 * 60, 16 * 60 + 30),# Wednesday 16:00 to 16:30
    (3, 10 * 60, 11 * 60),     # Thursday 10:00 to 11:00
    (3, 11 * 60 + 30, 15 * 60),# Thursday 11:30 to 15:00
    (3, 15 * 60 + 30, 16 * 60),# Thursday 15:30 to 16:00
    (3, 16 * 60 + 30, 17 * 60) # Thursday 16:30 to 17:00
]

# Define William's busy times
william_busy_times = [
    (0, 9 * 60 + 30, 11 * 60),# Monday 9:30 to 11:00
    (0, 11 * 60 + 30, 17 * 60),# Monday 11:30 to 17:00
    (1, 9 * 60, 13 * 60),      # Tuesday 9:00 to 13:00
    (1, 13 * 60 + 30, 16 * 60), # Tuesday 13:30 to 16:00
    (2, 9 * 60, 12 * 60 + 30), # Wednesday 9:00 to 12:30
    (2, 13 * 60, 14 * 60 + 30),# Wednesday 13:00 to 14:30
    (2, 15 * 60 + 30, 16 * 60), # Wednesday 15:30 to 16:00
    (2, 16 * 60 + 30, 17 * 60), # Wednesday 16:30 to 17:00
    (3, 9 * 60, 10 * 60 + 30), # Thursday 9:00 to 10:30
    (3, 11 * 60, 11 * 60 + 30),# Thursday 11:00 to 11:30
    (3, 12 * 60, 12 * 60 + 30),# Thursday 12:00 to 12:30
    (3, 13 * 60, 14 * 60),     # Thursday 13:00 to 14:00
    (3, 15 * 60, 17 * 60)      # Thursday 15:00 to 17:00
]

# Add constraints to avoid busy times
for d, s, e in natalie_busy_times:
    solver.add(Or(day != d, Or(start_time + meeting_duration <= s, start_time >= e)))

for d, s, e in william_busy_times:
    solver.add(Or(day != d, Or(start_time + meeting_duration <= s, start_time >= e)))

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    day_value = model[day].as_long()
    start_time_value = model[start_time].as_long()
    end_time_value = start_time_value + meeting_duration

    # Convert day number to string
    days = ["Monday", "Tuesday", "Wednesday", "Thursday"]
    day_str = days[day_value]

    # Convert time from minutes to HH:MM format
    start_time_str = f"{start_time_value // 60:02}:{start_time_value % 60:02}"
    end_time_str = f"{end_time_value // 60:02}:{end_time_value % 60:02}"

    print(f"SOLUTION:\nDay: {day_str}\nStart Time: {start_time_str}\nEnd Time: {end_time_str}")
else:
    print("No solution found")