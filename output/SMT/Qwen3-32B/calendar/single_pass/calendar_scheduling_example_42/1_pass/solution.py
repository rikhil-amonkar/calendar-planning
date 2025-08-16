import z3

solver = z3.Solver()

S = z3.Int('S')

solver.add(S >= 540)  # 9:00 AM in minutes
solver.add(S <= 960)  # 4:00 PM in minutes (meeting ends at 5:00 PM)

# All blocked intervals in minutes since midnight
blocked_intervals = [
    # Julie's blocked intervals
    (540, 570), (660, 690), (720, 750), (810, 840), (960, 1020),
    # Sean's blocked intervals
    (540, 570), (780, 810), (900, 930), (960, 990),
    # Lori's blocked intervals
    (600, 630), (660, 780), (930, 1020)
]

for start, end in blocked_intervals:
    solver.add(z3.Or(S + 60 <= start, S >= end))

if solver.check() == z3.sat:
    model = solver.model()
    s_val = model[S].as_long()
    hours = s_val // 60
    minutes = s_val % 60
    start_time = f"{hours:02d}:{minutes:02d}"
    end_time = f"{hours + 1:02d}:{minutes:02d}"
    print("SOLUTION:")
    print(f"Day: Monday")
    print(f"Start Time: {start_time}")
    print(f"End Time: {end_time}")
else:
    print("No solution found.")