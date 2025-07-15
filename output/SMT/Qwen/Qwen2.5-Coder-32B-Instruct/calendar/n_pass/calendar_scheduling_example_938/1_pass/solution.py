from z3 import *

# Define the variables
day = Int('day')  # 1 for Monday, 2 for Tuesday, ..., 5 for Friday
start_time = Int('start_time')  # in minutes from 00:00

# Constants for days
MONDAY = 1
TUESDAY = 2
WEDNESDAY = 3
THURSDAY = 4
FRIDAY = 5

# Meeting duration in minutes
meeting_duration = 30

# Define the constraints
constraints = []

# Day constraints
constraints.append(And(day >= MONDAY, day <= FRIDAY))

# Start time constraints (between 9:00 and 17:00)
constraints.append(And(start_time >= 9 * 60, start_time <= 17 * 60 - meeting_duration))

# Eugene's busy times
eugene_busy_times = [
    (MONDAY, 11 * 60, 12 * 60),
    (MONDAY, 13 * 60 + 30, 14 * 60),
    (MONDAY, 14 * 60 + 30, 15 * 60),
    (MONDAY, 16 * 60, 16 * 60 + 30),
    (WEDNESDAY, 9 * 60, 9 * 60 + 30),
    (WEDNESDAY, 11 * 60, 11 * 60 + 30),
    (WEDNESDAY, 12 * 60, 12 * 60 + 30),
    (WEDNESDAY, 13 * 60 + 30, 15 * 60),
    (THURSDAY, 9 * 60 + 30, 10 * 60),
    (THURSDAY, 11 * 60, 12 * 60 + 30),
    (FRIDAY, 10 * 60 + 30, 11 * 60),
    (FRIDAY, 12 * 60, 12 * 60 + 30),
    (FRIDAY, 13 * 60, 13 * 60 + 30)
]

for d, s, e in eugene_busy_times:
    constraints.append(Or(day != d, Or(start_time + meeting_duration <= s, start_time >= e)))

# Eric's busy times
eric_busy_times = [
    (MONDAY, 9 * 60, 17 * 60),
    (TUESDAY, 9 * 60, 17 * 60),
    (WEDNESDAY, 9 * 60, 11 * 60 + 30),
    (WEDNESDAY, 12 * 60, 14 * 60),
    (WEDNESDAY, 14 * 60 + 30, 16 * 60 + 30),
    (THURSDAY, 9 * 60, 17 * 60),
    (FRIDAY, 9 * 60, 11 * 60),
    (FRIDAY, 11 * 60 + 30, 17 * 60)
]

for d, s, e in eric_busy_times:
    constraints.append(Or(day != d, Or(start_time + meeting_duration <= s, start_time >= e)))

# Eric's preference to avoid Wednesday
constraints.append(day != WEDNESDAY)

# Solve the problem
s = Solver()
s.add(constraints)

if s.check() == sat:
    m = s.model()
    day_value = m[day].as_long()
    start_time_value = m[start_time].as_long()
    end_time_value = start_time_value + meeting_duration

    day_str = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"][day_value - 1]
    start_time_str = f"{start_time_value // 60:02}:{start_time_value % 60:02}"
    end_time_str = f"{end_time_value // 60:02}:{end_time_value % 60:02}"

    print(f"SOLUTION:\nDay: {day_str}\nStart Time: {start_time_str}\nEnd Time: {end_time_str}")
else:
    print("No solution found")