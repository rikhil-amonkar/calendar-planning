import z3

solver = z3.Solver()

start = z3.Int('start')

# Work hours from 9:00 (540) to 17:00 (1020), meeting is 30 min
solver.add(start >= 540)
solver.add(start + 30 <= 1020)

# Blocked intervals for each participant
blocked_intervals = [
    # Doris
    (540, 660), (810, 840), (960, 990),
    # Theresa
    (600, 720),
    # Terry
    (570, 600), (690, 720), (750, 780), (810, 840), (870, 900), (930, 1020),
    # Carolyn
    (540, 630), (660, 690), (720, 780), (810, 870), (900, 1020),
    # Kyle
    (540, 570), (690, 720), (750, 780), (870, 1020)
]

for b_start, b_end in blocked_intervals:
    solver.add(z3.Or(start + 30 <= b_start, start >= b_end))

if solver.check() == z3.sat:
    model = solver.model()
    start_time = model[start].as_long()
    day = "Monday"
    start_hh = start_time // 60
    start_mm = start_time % 60
    end_time = start_time + 30
    end_hh = end_time // 60
    end_mm = end_time % 60
    time_str = f"{start_hh:02d}:{start_mm:02d}:{end_hh:02d}:{end_mm:02d}"
    print(f"{{{time_str}}} {day}")
else:
    print("No solution found")