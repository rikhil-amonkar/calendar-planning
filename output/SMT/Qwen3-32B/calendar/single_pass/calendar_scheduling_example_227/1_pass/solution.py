from z3 import *

solver = Solver()

t = Int('t')

# Work hours: 9:00 (540) to 17:00 (1020). Meeting duration 30 mins. So t must be between 540 and 990 (inclusive)
solver.add(t >= 540)
solver.add(t <= 990)  # because t + 30 <= 1020 → t <= 990

# David's preference: not before 14:00 (840)
solver.add(t >= 840)

# All busy intervals
busy_intervals = [
    # David
    (690, 720),
    (870, 900),
    # Douglas
    (570, 600),
    (690, 720),
    (780, 810),
    (870, 900),
    # Ralph
    (540, 570),
    (600, 660),
    (690, 750),
    (810, 900),
    (930, 960),
    (990, 1020),
    # Jordan
    (540, 600),
    (720, 750),
    (780, 810),
    (870, 900),
    (930, 1020),
]

for b_start, b_end in busy_intervals:
    solver.add(Or(t >= b_end, t + 30 <= b_start))

if solver.check() == sat:
    model = solver.model()
    t_val = model[t].as_long()
    day = "Monday"
    start_time = t_val
    end_time = t_val + 30
    # Convert to HH:MM format
    def to_time_str(minutes):
        hours = minutes // 60
        mins = minutes % 60
        return f"{hours:02d}:{mins:02d}"
    print(f"SOLUTION:")
    print(f"Day: {day}")
    print(f"Start Time: {to_time_str(start_time)}")
    print(f"End Time: {to_time_str(end_time)}")
else:
    print("No solution found.")