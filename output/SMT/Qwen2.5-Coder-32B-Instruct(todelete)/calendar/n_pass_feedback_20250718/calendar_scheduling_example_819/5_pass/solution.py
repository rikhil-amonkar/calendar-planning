from z3 import *

# Define the variables
day = Int('day')  # 0 = Monday, 1 = Tuesday, 2 = Wednesday, 3 = Thursday
start_time = Int('start_time')  # in minutes from 00:00

# Define the constraints
# Meeting duration is 30 minutes
meeting_duration = 30

# Work hours are from 9:00 to 17:00 (540 to 1020 minutes from 00:00)
work_start = 540
work_end = 1020

# Julie has no meetings the whole week, so no additional constraints for her

# Ruth's busy times
ruth_busy_times = [
    (540, 1020),  # Monday
    (540, 1020),  # Tuesday
    (540, 1020),  # Wednesday
    (540, 690),   # Thursday 9:00 to 11:30
    (705, 855),   # Thursday 11:30 to 14:30
    (900, 1020)   # Thursday 15:00 to 17:00
]

# Define the solver
solver = Solver()

# Add constraints for the day
solver.add(day >= 0)
solver.add(day <= 3)

# Add constraints for the start time
solver.add(start_time >= work_start)
solver.add(start_time + meeting_duration <= work_end)

# Add Ruth's busy times constraints
for i, (busy_start, busy_end) in enumerate(ruth_busy_times):
    solver.add(Or(day != i, Or(start_time + meeting_duration <= busy_start, start_time >= busy_end)))

# Julie's preference to avoid meetings before 11:30 on Thursday
thursday_start = 690  # 11:30 in minutes from 00:00
solver.add(Or(day != 3, start_time >= thursday_start))

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    meeting_day = ["Monday", "Tuesday", "Wednesday", "Thursday"][model[day].as_long()]
    meeting_start = model[start_time].as_long()
    meeting_end = meeting_start + meeting_duration
    meeting_start_time = f"{meeting_start // 60:02}:{meeting_start % 60:02}"
    meeting_end_time = f"{meeting_end // 60:02}:{meeting_end % 60:02}"
    print(f"SOLUTION:\nDay: {meeting_day}\nStart Time: {meeting_start_time}\nEnd Time: {meeting_end_time}")
else:
    print("No solution found")