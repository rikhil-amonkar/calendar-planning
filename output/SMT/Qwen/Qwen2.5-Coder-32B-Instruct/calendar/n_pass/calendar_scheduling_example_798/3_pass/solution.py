from z3 import *

# Define the variables for the day and time
day = Int('day')  # 0 for Monday, 1 for Tuesday, 2 for Wednesday
start_time = Int('start_time')  # in minutes from 9:00

# Define the constraints
constraints = []

# Meeting duration is 30 minutes
meeting_duration = 30

# Work hours are from 9:00 to 17:00, so in minutes from 9:00, it's 0 to 480
work_start = 0
work_end = 480

# Day constraints: Only consider Tuesday and Wednesday
constraints.append(day >= 1)
constraints.append(day <= 2)

# Start time constraints within work hours
constraints.append(start_time >= work_start)
constraints.append(start_time + meeting_duration <= work_end)

# Nancy's schedule
nancy_busy_times = {
    0: [(10*60, 10*60+30), (11*60+30, 12*60+30), (13*60+30, 14*60), (14*60+30, 15*60+30), (16*60, 17*60)],
    1: [(9*60+30, 10*60+30), (11*60, 11*60+30), (12*60, 12*60+30), (13*60, 13*60+30), (15*60+30, 16*60)],
    2: [(10*60, 11*60+30), (13*60+30, 16*60)]
}

for d, times in nancy_busy_times.items():
    for s, e in times:
        constraints.append(Or(start_time + meeting_duration <= s, start_time >= e))

# Jose's schedule
jose_busy_times = {
    0: [(9*60, 17*60)],
    1: [(9*60, 9*60+30), (11*60, 11*60+30), (12*60, 12*60+30), (13*60, 13*60+30), (15*60+30, 16*60)],
    2: [(9*60, 9*60+30), (10*60, 12*60+30), (13*60+30, 14*60+30), (15*60, 17*60)]
}

for d, times in jose_busy_times.items():
    for s, e in times:
        constraints.append(Or(start_time + meeting_duration <= s, start_time >= e))

# Solve the constraints
solver = Solver()
solver.add(constraints)

if solver.check() == sat:
    model = solver.model()
    day_value = model[day].as_long()
    start_time_value = model[start_time].as_long()
    end_time_value = start_time_value + meeting_duration
    
    day_str = ["Monday", "Tuesday", "Wednesday"][day_value]
    start_time_str = f"{(start_time_value // 60 + 9):02}:{(start_time_value % 60):02}"
    end_time_str = f"{(end_time_value // 60 + 9):02}:{(end_time_value % 60):02}"
    
    print(f"SOLUTION:\nDay: {day_str}\nStart Time: {start_time_str}\nEnd Time: {end_time_str}")
else:
    print("No solution found")