from z3 import Solver, Int, Or, And, Implies, sat

solver = Solver()
day = Int('day')
start_time = Int('start_time')

# Day must be Tuesday (1) to avoid Monday
solver.add(day == 1)

# Time constraints (minutes since 9:00)
solver.add(start_time >= 0, start_time <= 450)  # 9:00-16:30 (max start for 30min meeting)

# Harold's preferences: Tuesday after 14:30 (330 minutes)
solver.add(start_time >= 330)

# Harold's Tuesday busy periods (minutes since 9:00)
busy_periods = [
    (0, 30),     # 9:00-9:30
    (90, 150),   # 10:30-11:30
    (210, 270),  # 12:30-13:30
    (330, 390),  # 14:30-15:30
    (420, 480)   # 16:00-17:00
]

# Add constraints to avoid overlapping with Harold's busy times
for (busy_start, busy_end) in busy_periods:
    solver.add(Or(start_time + 30 <= busy_start, start_time >= busy_end))

# Jeffrey has no constraints

if solver.check() == sat:
    m = solver.model()
    t = m[start_time].as_long()
    hours = 9 + t // 60
    minutes = t % 60
    print(f"Meeting starts on Tuesday at {hours:02d}:{minutes:02d}")
else:
    print("No valid time found")