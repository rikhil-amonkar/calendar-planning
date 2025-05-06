from z3 import Solver, Int, Or, sat

solver = Solver()
start = Int('start')

# Define the time constraints (in minutes since 9:00)
min_time = 0  # 9:00
max_time = 420  # 17:00 - 1 hour = 16:00 (420 minutes)

solver.add(start >= min_time, start <= max_time)

# James's busy periods (in minutes since 9:00)
james_busy = [
    (150, 180),   # 11:30-12:00
    (330, 360),    # 14:30-15:00
]

# John's busy periods
john_busy = [
    (30, 120),     # 9:30-11:00
    (150, 180),    # 11:30-12:00
    (210, 270),    # 12:30-13:30
    (330, 450),    # 14:30-16:30
]

# Add constraints for James
for (busy_start, busy_end) in james_busy:
    solver.add(Or(start + 60 <= busy_start, start >= busy_end))

# Add constraints for John
for (busy_start, busy_end) in john_busy:
    solver.add(Or(start + 60 <= busy_start, start >= busy_end))

# Check for a solution and print the time
if solver.check() == sat:
    m = solver.model()
    start_min = m[start].as_long()
    hours = 9 + start_min // 60
    minutes = start_min % 60
    print(f"Meeting starts at {hours:02d}:{minutes:02d}")
else:
    print("No valid time found")