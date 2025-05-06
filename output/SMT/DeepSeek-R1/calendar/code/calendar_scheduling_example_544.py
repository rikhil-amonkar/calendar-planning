from z3 import Solver, Int, Or, sat

solver = Solver()
start = Int('start')

# Define the time constraints (in minutes since 9:00)
min_time = 0          # 9:00
max_time = 90         # 11:00 - 0.5 hour = 10:30 (90 minutes)

solver.add(start >= min_time, start <= max_time)

# Albert's busy periods (in minutes since 9:00)
albert_busy = [
    (0, 60),    # 9:00-10:00
    (90, 180),  # 10:30-12:00
    (360, 450)  # 15:00-16:30
]

# Add constraints for Albert (meeting must not overlap with busy periods)
for (busy_start, busy_end) in albert_busy:
    solver.add(Or(start + 30 <= busy_start, start >= busy_end))

# Deborah has no busy periods, so no additional constraints

# Check for a solution and print the time
if solver.check() == sat:
    m = solver.model()
    start_min = m[start].as_long()
    hours = 9 + start_min // 60
    minutes = start_min % 60
    print(f"Meeting starts at {hours:02d}:{minutes:02d}")
else:
    print("No valid time found")