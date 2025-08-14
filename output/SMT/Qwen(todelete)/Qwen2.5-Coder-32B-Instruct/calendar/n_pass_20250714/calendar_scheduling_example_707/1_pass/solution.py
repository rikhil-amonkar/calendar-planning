from z3 import *

# Define variables
day = Int('day')  # 0 = Monday, 1 = Tuesday, 2 = Wednesday
start_time = Int('start_time')  # in minutes from 9:00

# Constants for time slots
meeting_duration = 30  # 30 minutes
work_start = 9 * 60  # 9:00 in minutes
work_end = 17 * 60  # 17:00 in minutes

# Constraints for each person's availability
ryan_busy_times = [
    (9*60 + 30, 10*60), (11*60, 12*60), (13*60, 13*60 + 30), (15*60 + 30, 16*60),
    (11*60 + 30, 12*60 + 30), (15*60 + 30, 16*60),
    (12*60, 13*60), (15*60 + 30, 16*60), (16*60 + 30, 17*60)
]

adam_busy_times = [
    (9*60, 10*60 + 30), (11*60, 13*60 + 30), (14*60, 16*60), (16*60 + 30, 17*60),
    (9*60, 10*60), (10*60 + 30, 15*60 + 30), (16*60, 17*60),
    (9*60, 9*60 + 30), (10*60, 11*60), (11*60 + 30, 14*60 + 30), (15*60, 15*60 + 30), (16*60, 16*60 + 30)
]

# Create a solver instance
s = Solver()

# Add constraints for the day
s.add(day >= 0)
s.add(day <= 2)

# Add constraints for the start time
s.add(start_time >= work_start)
s.add(start_time + meeting_duration <= work_end)

# Add constraints for Ryan's availability
for start, end in ryan_busy_times:
    s.add(Or(start_time + meeting_duration <= start, start_time >= end))

# Add constraints for Adam's availability
for start, end in adam_busy_times:
    s.add(Or(start_time + meeting_duration <= start, start_time >= end))

# Add constraint that Ryan cannot meet on Wednesday
s.add(day != 2)

# Solve the problem
if s.check() == sat:
    m = s.model()
    day_value = m[day].as_long()
    start_time_value = m[start_time].as_long()
    end_time_value = start_time_value + meeting_duration

    # Convert day number to string
    days = ["Monday", "Tuesday", "Wednesday"]
    day_str = days[day_value]

    # Convert start and end times to HH:MM format
    start_time_str = f"{(start_time_value // 60):02}:{(start_time_value % 60):02}"
    end_time_str = f"{(end_time_value // 60):02}:{(end_time_value % 60):02}"

    # Print the solution
    print(f"SOLUTION:\nDay: {day_str}\nStart Time: {start_time_str}\nEnd Time: {end_time_str}")
else:
    print("No solution found")