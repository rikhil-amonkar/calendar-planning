from z3 import *

# Define the variables
day = Int('day')  # 0 = Monday, 1 = Tuesday, 2 = Wednesday
start_time = Int('start_time')  # in minutes from 9:00

# Define the constraints
# Meeting duration is 30 minutes
meeting_duration = 30

# Define the work hours in minutes from 9:00
work_start = 0
work_end = 480  # 17:00 - 9:00 = 8 hours = 480 minutes

# Define the busy times for Tyler and Ruth
tyler_busy_times = [
    (1, 0, 30),  # Tuesday 9:00 - 9:30
    (1, 330, 60),  # Tuesday 14:30 - 15:00
    (2, 630, 30),  # Wednesday 10:30 - 11:00
    (2, 750, 60),  # Wednesday 12:30 - 13:00
    (2, 810, 60),  # Wednesday 13:30 - 14:00
    (2, 990, 90)   # Wednesday 16:30 - 17:00
]

ruth_busy_times = [
    (0, 0, 60),  # Monday 9:00 - 10:00
    (0, 60, 120),  # Monday 10:00 - 12:00
    (0, 150, 120),  # Monday 12:30 - 14:30
    (0, 300, 60),  # Monday 15:00 - 16:00
    (0, 390, 90),  # Monday 16:30 - 17:00
    (1, 0, 480),  # Tuesday 9:00 - 17:00
    (2, 0, 480)   # Wednesday 9:00 - 17:00
]

# Tyler's preference: avoid meetings on Monday before 16:00
tyler_preference = Or(day != 0, start_time >= 420)  # 16:00 - 9:00 = 7 hours = 420 minutes

# Define the solver
solver = Solver()

# Add constraints for the day
solver.add(day >= 0)
solver.add(day <= 2)

# Add constraints for the start time
solver.add(start_time >= work_start)
solver.add(start_time + meeting_duration <= work_end)

# Add constraints for Tyler's busy times
for d, s, d in tyler_busy_times:
    solver.add(Or(day != d, Or(start_time >= s + d, start_time + meeting_duration <= s)))

# Add constraints for Ruth's busy times
for d, s, d in ruth_busy_times:
    solver.add(Or(day != d, Or(start_time >= s + d, start_time + meeting_duration <= s)))

# Add Tyler's preference
solver.add(tyler_preference)

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    meeting_day = ["Monday", "Tuesday", "Wednesday"][model[day].as_long()]
    meeting_start_time = 9 + model[start_time].as_long() // 60
    meeting_start_minute = model[start_time].as_long() % 60
    meeting_end_time = meeting_start_time + meeting_duration // 60
    meeting_end_minute = meeting_start_minute + meeting_duration % 60
    if meeting_end_minute >= 60:
        meeting_end_minute -= 60
        meeting_end_time += 1

    print(f"SOLUTION:")
    print(f"Day: {meeting_day}")
    print(f"Start Time: {meeting_start_time:02}:{meeting_start_minute:02}")
    print(f"End Time: {meeting_end_time:02}:{meeting_end_minute:02}")
else:
    print("No solution found")