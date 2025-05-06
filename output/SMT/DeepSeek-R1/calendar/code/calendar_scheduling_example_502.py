from z3 import Solver, Int, Or, sat

solver = Solver()
start = Int('start')

# Define time constraints (in minutes since 9:00)
min_time = 0           # 9:00
max_time = 450         # 16:30 (latest start for 30min meeting)
solver.add(start >= min_time, start <= max_time)

# Jack's preference: meeting must end by 12:30 (210 minutes)
solver.add(start + 30 <= 210)

# Jack's busy periods (minutes since 9:00)
jack_busy = [
    (30, 90),    # 9:30-10:30
    (120, 150),  # 11:00-11:30
    (210, 240),  # 12:30-13:00
    (300, 330),  # 14:00-14:30
    (420, 450)   # 16:00-16:30
]

# Charlotte's busy periods (minutes since 9:00)
charlotte_busy = [
    (30, 60),    # 9:30-10:00
    (90, 180),   # 10:30-12:00
    (210, 270),  # 12:30-13:30
    (300, 420)   # 14:00-16:00
]

# Add constraints for Jack's busy periods
for (busy_start, busy_end) in jack_busy:
    solver.add(Or(start + 30 <= busy_start, start >= busy_end))

# Add constraints for Charlotte's busy periods
for (busy_start, busy_end) in charlotte_busy:
    solver.add(Or(start + 30 <= busy_start, start >= busy_end))

# Check for solution
if solver.check() == sat:
    m = solver.model()
    start_min = m[start].as_long()
    hours = 9 + start_min // 60
    minutes = start_min % 60
    print(f"Meeting starts at {hours:02d}:{minutes:02d}")
else:
    print("No valid time found")