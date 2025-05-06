from z3 import Solver, Int, Or, sat

solver = Solver()
start = Int('start')

# Define the time constraints (in minutes since 9:00)
min_time = 0          # 9:00
max_time = 450         # 17:00 - 0.5 hour = 16:30 (450 minutes)

solver.add(start >= min_time, start <= max_time)

# Doris's busy periods (in minutes since 9:00)
doris_busy = [
    (0, 120),    # 9:00-11:00
    (270, 300),   # 13:30-14:00
    (420, 450)    # 16:00-16:30
]

# Theresa's busy periods
theresa_busy = [
    (60, 180)     # 10:00-12:00
]

# Terry's busy periods
terry_busy = [
    (30, 60),     # 9:30-10:00
    (150, 180),   # 11:30-12:00
    (210, 240),   # 12:30-13:00
    (270, 300),   # 13:30-14:00
    (330, 360),   # 14:30-15:00
    (390, 480)    # 15:30-17:00
]

# Carolyn's busy periods
carolyn_busy = [
    (0, 90),      # 9:00-10:30
    (120, 150),   # 11:00-11:30
    (180, 240),   # 12:00-13:00
    (270, 330),   # 13:30-14:30
    (360, 480)    # 15:00-17:00
]

# Kyle's busy periods
kyle_busy = [
    (0, 30),      # 9:00-9:30
    (150, 180),   # 11:30-12:00
    (210, 240),   # 12:30-13:00
    (330, 480)    # 14:30-17:00
]

# Add constraints for each person's busy periods
for (busy_start, busy_end) in doris_busy:
    solver.add(Or(start + 30 <= busy_start, start >= busy_end))

for (busy_start, busy_end) in theresa_busy:
    solver.add(Or(start + 30 <= busy_start, start >= busy_end))

for (busy_start, busy_end) in terry_busy:
    solver.add(Or(start + 30 <= busy_start, start >= busy_end))

for (busy_start, busy_end) in carolyn_busy:
    solver.add(Or(start + 30 <= busy_start, start >= busy_end))

for (busy_start, busy_end) in kyle_busy:
    solver.add(Or(start + 30 <= busy_start, start >= busy_end))

# Check for a solution and print the time
if solver.check() == sat:
    m = solver.model()
    start_min = m[start].as_long()
    hours = 9 + start_min // 60
    minutes = start_min % 60
    print(f"Meeting starts at {hours:02d}:{minutes:02d}")
else:
    print("No valid time found")