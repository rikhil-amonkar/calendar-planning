from z3 import *

# Define the variables for the day and time
day = Int('day')  # 0=Monday, 1=Tuesday, 2=Wednesday, 3=Thursday
start_time = Int('start_time')  # in minutes from 9:00

# Define the meeting duration
meeting_duration = 30  # in minutes

# Define the constraints for each participant
def is_available(day, start_time, end_time, busy_times):
    return And([Or(start_time + meeting_duration <= busy_start, start_time >= busy_end) for busy_start, busy_end in busy_times])

# Busy times for Mary and Alexis
mary_busy_times = [
    (1, 60, 90),  # Tuesday 10:00 - 10:30
    (1, 930, 960),  # Tuesday 15:30 - 16:00
    (2, 30, 60),  # Wednesday 9:30 - 10:00
    (2, 900, 930),  # Wednesday 15:00 - 15:30
    (3, 0, 60),  # Thursday 9:00 - 10:00
    (3, 90, 120)  # Thursday 10:30 - 11:30
]

alexis_busy_times = [
    (0, 0, 60),  # Monday 9:00 - 10:00
    (0, 60, 78),  # Monday 10:30 - 12:00
    (0, 78, 990),  # Monday 12:30 - 16:30
    (1, 0, 60),  # Tuesday 9:00 - 10:00
    (1, 60, 78),  # Tuesday 10:30 - 11:30
    (1, 72, 930),  # Tuesday 12:00 - 15:30
    (1, 960, 990),  # Tuesday 16:00 - 17:00
    (2, 0, 78),  # Wednesday 9:00 - 11:00
    (2, 78, 990),  # Wednesday 11:30 - 17:00
    (3, 60, 78),  # Thursday 10:00 - 12:00
    (3, 840, 870),  # Thursday 14:00 - 14:30
    (3, 930, 960),  # Thursday 15:30 - 16:00
    (3, 990, 990)  # Thursday 16:30 - 17:00
]

# Convert busy times to minutes from 9:00
mary_busy_times_minutes = [(d, s - 540, e - 540) for d, s, e in mary_busy_times]
alexis_busy_times_minutes = [(d, s - 540, e - 540) for d, s, e in alexis_busy_times]

# Create the solver
solver = Solver()

# Add constraints for the day and time
solver.add(Or(day == 0, day == 1, day == 2, day == 3))  # Monday to Thursday
solver.add(start_time >= 0)  # Start time must be after 9:00
solver.add(start_time + meeting_duration <= 480)  # End time must be before 17:00

# Add constraints for Mary's availability
for d, s, e in mary_busy_times_minutes:
    solver.add(is_available(day, start_time, start_time + meeting_duration, [(s, e)]))

# Add constraints for Alexis's availability
for d, s, e in alexis_busy_times_minutes:
    solver.add(is_available(day, start_time, start_time + meeting_duration, [(s, e)]))

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    day_value = model[day].as_long()
    start_time_value = model[start_time].as_long()
    end_time_value = start_time_value + meeting_duration
    
    # Convert day value to string
    days = ["Monday", "Tuesday", "Wednesday", "Thursday"]
    day_str = days[day_value]
    
    # Convert start and end times to HH:MM format
    start_time_str = f"{(start_time_value // 60 + 9):02}:{(start_time_value % 60):02}"
    end_time_str = f"{(end_time_value // 60 + 9):02}:{(end_time_value % 60):02}"
    
    print(f"SOLUTION:\nDay: {day_str}\nStart Time: {start_time_str}\nEnd Time: {end_time_str}")
else:
    print("No solution found")