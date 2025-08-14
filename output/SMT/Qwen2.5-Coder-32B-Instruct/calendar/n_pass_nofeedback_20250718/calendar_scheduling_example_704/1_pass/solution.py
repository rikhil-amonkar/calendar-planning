from z3 import *

# Define the variables
day = Int('day')  # 0 = Monday, 1 = Tuesday, 2 = Wednesday
start_time = Int('start_time')  # in minutes from 9:00

# Define the constraints
# Work hours are from 9:00 to 17:00, so start_time should be between 0 and 480 (10 hours * 60 minutes)
constraints = [
    day >= 0, day <= 2,
    start_time >= 0, start_time <= 480,
    start_time + 30 <= 480  # Meeting duration is 30 minutes
]

# Samuel's busy times
samuel_busy_times = [
    (10*60 + 30, 11*60),  # Monday 10:30 to 11:00
    (12*60, 12*60 + 30),    # Monday 12:00 to 12:30
    (13*60, 15*60),        # Monday 13:00 to 15:00
    (15*60 + 30, 16*60 + 30), # Monday 15:30 to 16:30
    (9*60, 12*60),         # Tuesday 9:00 to 12:00
    (14*60, 15*60 + 30),   # Tuesday 14:00 to 15:30
    (16*60 + 30, 17*60),   # Tuesday 16:30 to 17:00
    (10*60 + 30, 11*60),  # Wednesday 10:30 to 11:00
    (11*60 + 30, 12*60),  # Wednesday 11:30 to 12:00
    (12*60 + 30, 13*60),  # Wednesday 12:30 to 13:00
    (14*60, 14*60 + 30),  # Wednesday 14:00 to 14:30
    (15*60, 16*60)         # Wednesday 15:00 to 16:00
]

# Add constraints to avoid Samuel's busy times
for busy_start, busy_end in samuel_busy_times:
    constraints.append(Or(day != 0, Or(start_time + 30 <= busy_start, start_time >= busy_end)))
    constraints.append(Or(day != 1, Or(start_time + 30 <= busy_start, start_time >= busy_end)))
    constraints.append(Or(day != 2, Or(start_time + 30 <= busy_start, start_time >= busy_end)))

# Larry would rather not meet on Wednesday
constraints.append(day != 2)

# Samuel would like to avoid more meetings on Tuesday
constraints.append(day != 1)

# Create a solver and add the constraints
solver = Solver()
solver.add(constraints)

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    day_value = model[day].as_long()
    start_time_value = model[start_time].as_long()
    end_time_value = start_time_value + 30

    # Convert day and time to human-readable format
    days = ["Monday", "Tuesday", "Wednesday"]
    start_time_str = f"{(start_time_value // 60 + 9):02}:{(start_time_value % 60):02}"
    end_time_str = f"{(end_time_value // 60 + 9):02}:{(end_time_value % 60):02}"

    print(f"SOLUTION:\nDay: {days[day_value]}\nStart Time: {start_time_str}\nEnd Time: {end_time_str}")
else:
    print("No solution found")