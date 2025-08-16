from z3 import *

# Initialize solver
solver = Solver()

# Define the start time variable (in minutes since midnight)
S = Int('S')

# Work hours are 9:00 (540) to 17:00 (1020), meeting is 30 min, so S must be <= 990
solver.add(S >= 540, S <= 990)

# Collect all busy intervals for constrained participants
busy_intervals = []

# Stephanie's busy intervals
busy_intervals.extend([
    (660, 690),  # 11:00-11:30
    (870, 900)   # 14:30-15:00
])

# Joe's busy intervals
busy_intervals.extend([
    (540, 570),   # 9:00-9:30
    (600, 720),   # 10:00-12:00
    (750, 780),   # 12:30-13:00
    (840, 1020)   # 14:00-17:00
])

# Diana's busy intervals
busy_intervals.extend([
    (540, 630),   # 9:00-10:30
    (690, 720),   # 11:30-12:00
    (780, 840),   # 13:00-14:00
    (870, 930),   # 14:30-15:30
    (960, 1020)   # 16:00-17:00
])

# Deborah's busy intervals
busy_intervals.extend([
    (540, 600),   # 9:00-10:00
    (630, 720),   # 10:30-12:00
    (750, 780),   # 12:30-13:00
    (810, 840),   # 13:30-14:00
    (870, 930),   # 14:30-15:30
    (960, 990)    # 16:00-16:30
])

# Add constraints for each busy interval
for start, end in busy_intervals:
    solver.add(Or(S + 30 <= start, S >= end))

# Check for solution
if solver.check() == sat:
    model = solver.model()
    s_val = model[S].as_long()
    # Convert start time to HH:MM format
    start_hours = s_val // 60
    start_minutes = s_val % 60
    start_time = f"{start_hours:02d}:{start_minutes:02d}"
    # End time is start + 30 minutes
    end_val = s_val + 30
    end_hours = end_val // 60
    end_minutes = end_val % 60
    end_time = f"{end_hours:02d}:{end_minutes:02d}"
    # Output the solution
    print("SOLUTION:")
    print(f"Day: Monday")
    print(f"Start Time: {start_time}")
    print(f"End Time: {end_time}")
else:
    print("No solution found.")