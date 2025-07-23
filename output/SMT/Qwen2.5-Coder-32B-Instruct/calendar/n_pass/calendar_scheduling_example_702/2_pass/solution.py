from z3 import *

# Define the variables
day = Int('day')  # 0 = Monday, 1 = Tuesday, 2 = Wednesday
start_time = Int('start_time')  # in minutes from 9:00

# Define the constraints
constraints = []

# Work hours are from 9:00 to 17:00, so start_time should be between 0 and 480 (17:00 - 9:00 = 8 hours = 480 minutes)
constraints.append(start_time >= 0)
constraints.append(start_time <= 480)

# Meeting duration is 30 minutes
meeting_duration = 30

# Robert's busy times
robert_busy_times = [
    (0, 11*60, 11*60 + 30),  # Monday 11:00 to 11:30
    (0, 14*60, 14*60 + 30),  # Monday 14:00 to 14:30
    (0, 15*60 + 30, 16*60),  # Monday 15:30 to 16:00
    (1, 10*60 + 30, 11*60),  # Tuesday 10:30 to 11:00
    (1, 15*60, 15*60 + 30),  # Tuesday 15:00 to 15:30
    (2, 10*60, 11*60),  # Wednesday 10:00 to 11:00
    (2, 11*60 + 30, 12*60),  # Wednesday 11:30 to 12:00
    (2, 12*60 + 30, 13*60),  # Wednesday 12:30 to 13:00
    (2, 13*60 + 30, 14*60),  # Wednesday 13:30 to 14:00
    (2, 15*60, 15*60 + 30),  # Wednesday 15:00 to 15:30
    (2, 16*60, 16*60 + 30)  # Wednesday 16:00 to 16:30
]

# Ralph's busy times
ralph_busy_times = [
    (0, 10*60, 13*60 + 30),  # Monday 10:00 to 13:30
    (0, 14*60, 14*60 + 30),  # Monday 14:00 to 14:30
    (0, 15*60, 17*60),  # Monday 15:00 to 17:00
    (1, 9*60, 9*60 + 30),  # Tuesday 9:00 to 9:30
    (1, 10*60, 10*60 + 30),  # Tuesday 10:00 to 10:30
    (1, 11*60, 11*60 + 30),  # Tuesday 11:00 to 11:30
    (1, 12*60, 13*60),  # Tuesday 12:00 to 13:00
    (1, 14*60, 15*60 + 30),  # Tuesday 14:00 to 15:30
    (1, 16*60, 17*60),  # Tuesday 16:00 to 17:00
    (2, 10*60 + 30, 11*60),  # Wednesday 10:30 to 11:00
    (2, 11*60 + 30, 12*60),  # Wednesday 11:30 to 12:00
    (2, 13*60, 14*60 + 30),  # Wednesday 13:00 to 14:30
    (2, 16*60 + 30, 17*60)  # Wednesday 16:30 to 17:00
]

# Add constraints to avoid busy times
for d, s, e in robert_busy_times:
    constraints.append(Or(day != d, Or(start_time + meeting_duration <= s, start_time >= e)))

for d, s, e in ralph_busy_times:
    constraints.append(Or(day != d, Or(start_time + meeting_duration <= s, start_time >= e)))

# Robert prefers not to have meetings on Monday, so we add a soft constraint to minimize the day
# We can do this by adding a penalty for choosing Monday
penalty = If(day == 0, 1, 0)

# Create the solver
solver = Optimize()

# Add the constraints
solver.add(constraints)

# Minimize the penalty (i.e., prefer not Monday)
solver.minimize(penalty)

# Check if the problem is solvable
if solver.check() == sat:
    model = solver.model()
    meeting_day = model[day].as_long()
    meeting_start_time = model[start_time].as_long()
    meeting_end_time = meeting_start_time + meeting_duration

    # Convert day number to string
    days = ["Monday", "Tuesday", "Wednesday"]
    if 0 <= meeting_day < len(days):
        meeting_day_str = days[meeting_day]
    else:
        meeting_day_str = "Invalid Day"

    # Convert start and end times to HH:MM format
    meeting_start_time_str = f"{9 + meeting_start_time // 60:02}:{meeting_start_time % 60:02}"
    meeting_end_time_str = f"{9 + meeting_end_time // 60:02}:{meeting_end_time % 60:02}"

    print(f"SOLUTION:\nDay: {meeting_day_str}\nStart Time: {meeting_start_time_str}\nEnd Time: {meeting_end_time_str}")
else:
    print("No solution found")