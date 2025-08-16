import z3

solver = z3.Solver()

start_time = z3.Int('start_time')

# Add global constraints for the meeting time (9:00 to 17:00, 30-minute meeting)
solver.add(start_time >= 540)  # 9:00 AM in minutes
solver.add(start_time <= 990)  # 16:30 in minutes (17:00 - 30 min)

# Define all busy intervals for each participant
busy_intervals = []

# Cynthia's busy intervals
busy_intervals.extend([
    (540, 570),  # 9:00-9:30
    (600, 630),  # 10:00-10:30
    (810, 870),  # 13:30-14:30
    (900, 960)   # 15:00-16:00
])

# Ann's busy intervals
busy_intervals.extend([
    (600, 660),  # 10:00-11:00
    (780, 810),  # 13:00-13:30
    (840, 900),  # 14:00-15:00
    (960, 990)   # 16:00-16:30
])

# Catherine's busy intervals
busy_intervals.extend([
    (540, 690),  # 9:00-11:30
    (750, 810),  # 12:30-13:30
    (870, 1020)  # 14:30-17:00
])

# Kyle's busy intervals
busy_intervals.extend([
    (540, 570),  # 9:00-9:30
    (600, 690),  # 10:00-11:30
    (720, 750),  # 12:00-12:30
    (780, 870),  # 13:00-14:30
    (900, 960)   # 15:00-16:00
])

# Add constraints for each busy interval
for s, e in busy_intervals:
    solver.add(z3.Or(start_time + 30 <= s, e <= start_time))

if solver.check() == z3.sat:
    model = solver.model()
    start_mins = model[start_time].as_long()
    end_mins = start_mins + 30
    day = "Monday"
    start_time_str = f"{start_mins//60:02d}:{start_mins%60:02d}"
    end_time_str = f"{end_mins//60:02d}:{end_mins%60:02d}"
    print(f"SOLUTION:\nDay: {day}\nStart Time: {start_time_str}\nEnd Time: {end_time_str}")
else:
    print("No solution found.")