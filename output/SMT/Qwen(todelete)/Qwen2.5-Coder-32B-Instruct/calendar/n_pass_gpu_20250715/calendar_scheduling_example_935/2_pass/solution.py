from z3 import *

# Define the variables
day = Int('day')  # 0=Monday, 1=Tuesday, 2=Wednesday, 3=Thursday, 4=Friday
start_time = Int('start_time')  # in minutes from 9:00

# Define the constants for the time slots
meeting_duration = 30  # 30 minutes
work_start = 9 * 60  # 9:00 in minutes
work_end = 17 * 60  # 17:00 in minutes

# Define the busy times for Terry and Frances
terry_busy_times = [
    (0, 10*60 + 30, 11*60),  # Monday 10:30 - 11:00
    (0, 12*60 + 30, 14*60),  # Monday 12:30 - 14:00
    (0, 15*60, 17*60),        # Monday 15:00 - 17:00
    (1, 9*60 + 30, 10*60),   # Tuesday 9:30 - 10:00
    (1, 10*60 + 30, 11*60),  # Tuesday 10:30 - 11:00
    (1, 14*60, 14*60 + 30),   # Tuesday 14:00 - 14:30
    (1, 16*60, 16*60 + 30),   # Tuesday 16:00 - 16:30
    (2, 9*60 + 30, 10*60),   # Wednesday 9:30 - 10:00
    (2, 11*60, 12*60),       # Wednesday 11:00 - 12:00
    (2, 13*60, 13*60 + 30),   # Wednesday 13:00 - 13:30
    (2, 15*60, 16*60),       # Wednesday 15:00 - 16:00
    (2, 16*60 + 30, 17*60),  # Wednesday 16:30 - 17:00
    (3, 9*60 + 30, 10*60),   # Thursday 9:30 - 10:00
    (3, 12*60, 12*60 + 30),   # Thursday 12:00 - 12:30
    (3, 13*60, 14*60 + 30),   # Thursday 13:00 - 14:30
    (3, 16*60, 16*60 + 30),   # Thursday 16:00 - 16:30
    (4, 9*60, 11*60 + 30),     # Friday 9:00 - 11:30
    (4, 12*60, 12*60 + 30),   # Friday 12:00 - 12:30
    (4, 13*60 + 30, 16*60),  # Friday 13:30 - 16:00
    (4, 16*60 + 30, 17*60)   # Friday 16:30 - 17:00
]

frances_busy_times = [
    (0, 9*60 + 30, 11*60),   # Monday 9:30 - 11:00
    (0, 11*60 + 30, 13*60),  # Monday 11:30 - 13:00
    (0, 14*60, 14*60 + 30),   # Monday 14:00 - 14:30
    (0, 15*60, 16*60),       # Monday 15:00 - 16:00
    (1, 9*60, 9*60 + 30),    # Tuesday 9:00 - 9:30
    (1, 10*60, 10*60 + 30),  # Tuesday 10:00 - 10:30
    (1, 11*60, 12*60),       # Tuesday 11:00 - 12:00
    (1, 13*60, 14*60 + 30),   # Tuesday 13:00 - 14:30
    (1, 15*60 + 30, 16*60),  # Tuesday 15:30 - 16:30
    (2, 9*60 + 30, 10*60),   # Wednesday 9:30 - 10:00
    (2, 10*60 + 30, 11*60),  # Wednesday 10:30 - 11:00
    (2, 11*60 + 30, 16*60),  # Wednesday 11:30 - 16:00
    (2, 16*60 + 30, 17*60),  # Wednesday 16:30 - 17:00
    (3, 11*60, 12*60 + 30),   # Thursday 11:00 - 12:30
    (3, 14*60 + 30, 17*60),  # Thursday 14:30 - 17:00
    (4, 9*60 + 30, 10*60),   # Friday 9:30 - 10:00
    (4, 11*60, 12*60 + 30),   # Friday 11:00 - 12:30
    (4, 13*60, 16*60),       # Friday 13:00 - 16:00
    (4, 16*60 + 30, 17*60)   # Friday 16:30 - 17:00
]

# Create the solver
solver = Solver()

# Add constraints for the day
solver.add(day >= 0)
solver.add(day <= 4)

# Add constraints for the start time
solver.add(start_time >= work_start)
solver.add(start_time + meeting_duration <= work_end)

# Add constraints for Terry's busy times
for d, s, e in terry_busy_times:
    solver.add(Or(day != d, Or(start_time + meeting_duration <= s, start_time >= e)))

# Add constraints for Frances's busy times
for d, s, e in frances_busy_times:
    solver.add(Or(day != d, Or(start_time + meeting_duration <= s, start_time >= e)))

# Prioritize days other than Tuesday
# Check for available slots on other days first
for d in range(5):
    if d != 1:  # Skip Tuesday
        solver.push()
        solver.add(day == d)
        if solver.check() == sat:
            model = solver.model()
            day_value = model[day].as_long()
            start_time_value = model[start_time].as_long()
            end_time_value = start_time_value + meeting_duration
            
            days_of_week = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]
            start_time_str = f"{start_time_value // 60:02}:{start_time_value % 60:02}"
            end_time_str = f"{end_time_value // 60:02}:{end_time_value % 60:02}"
            
            print(f"SOLUTION:\nDay: {days_of_week[day_value]}\nStart Time: {start_time_str}\nEnd Time: {end_time_str}")
            break
        solver.pop()

# If no slot is found on other days, check Tuesday
if solver.check() == sat:
    model = solver.model()
    day_value = model[day].as_long()
    start_time_value = model[start_time].as_long()
    end_time_value = start_time_value + meeting_duration
    
    days_of_week = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]
    start_time_str = f"{start_time_value // 60:02}:{start_time_value % 60:02}"
    end_time_str = f"{end_time_value // 60:02}:{end_time_value % 60:02}"
    
    print(f"SOLUTION:\nDay: {days_of_week[day_value]}\nStart Time: {start_time_str}\nEnd Time: {end_time_str}")
else:
    print("No solution found")