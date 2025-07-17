from z3 import *

# Define the variables
day = Int('day')  # 0 = Monday, 1 = Tuesday, 2 = Wednesday
start_time = Int('start_time')  # in minutes from 9:00

# Define the constraints
solver = Solver()

# Meeting duration is 30 minutes
meeting_duration = 30

# Define the work hours
work_start = 9 * 60  # 9:00 in minutes
work_end = 17 * 60  # 17:00 in minutes

# Arthur's schedule
arthur_meetings = [
    (0, 11 * 60, 11 * 60 + 30),  # Monday 11:00 to 11:30
    (0, 13 * 60 + 30, 14 * 60),  # Monday 13:30 to 14:00
    (0, 15 * 60, 15 * 60 + 30),  # Monday 15:00 to 15:30
    (1, 13 * 60, 13 * 60 + 30),  # Tuesday 13:00 to 13:30
    (1, 16 * 60, 16 * 60 + 30),  # Tuesday 16:00 to 16:30
    (2, 10 * 60, 10 * 60 + 30),  # Wednesday 10:00 to 10:30
    (2, 11 * 60, 11 * 60 + 30),  # Wednesday 11:00 to 11:30
    (2, 12 * 60, 12 * 60 + 30),  # Wednesday 12:00 to 12:30
    (2, 14 * 60, 14 * 60 + 30),  # Wednesday 14:00 to 14:30
    (2, 16 * 60, 16 * 60 + 30)   # Wednesday 16:00 to 16:30
]

# Michael's schedule
michael_meetings = [
    (0, 9 * 60, 12 * 60),  # Monday 9:00 to 12:00
    (0, 12 * 60 + 30, 13 * 60),  # Monday 12:30 to 13:00
    (0, 14 * 60, 14 * 60 + 30),  # Monday 14:00 to 14:30
    (0, 15 * 60, 17 * 60),  # Monday 15:00 to 17:00
    (1, 9 * 60 + 30, 11 * 60 + 30),  # Tuesday 9:30 to 11:30
    (1, 12 * 60, 13 * 60 + 30),  # Tuesday 12:00 to 13:30
    (1, 14 * 60, 15 * 60 + 30),  # Tuesday 14:00 to 15:30
    (2, 10 * 60, 12 * 60 + 30),  # Wednesday 10:00 to 12:30
    (2, 13 * 60, 13 * 60 + 30)  # Wednesday 13:00 to 13:30
]

# Arthur can't meet on Tuesday
solver.add(day != 1)

# Meeting must be within work hours
solver.add(start_time >= work_start)
solver.add(start_time + meeting_duration <= work_end)

# Meeting must not overlap with Arthur's meetings
for d, s, e in arthur_meetings:
    solver.add(Or(day != d, Or(start_time + meeting_duration <= s, start_time >= e)))

# Meeting must not overlap with Michael's meetings
for d, s, e in michael_meetings:
    solver.add(Or(day != d, Or(start_time + meeting_duration <= s, start_time >= e)))

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    day_value = model[day].as_long()
    start_time_value = model[start_time].as_long()
    end_time_value = start_time_value + meeting_duration

    # Convert day and time to human-readable format
    days = ["Monday", "Tuesday", "Wednesday"]
    start_hour = start_time_value // 60
    start_minute = start_time_value % 60
    end_hour = end_time_value // 60
    end_minute = end_time_value % 60

    print(f"SOLUTION:")
    print(f"Day: {days[day_value]}")
    print(f"Start Time: {start_hour:02}:{start_minute:02}")
    print(f"End Time: {end_hour:02}:{end_minute:02}")
else:
    print("No solution found")