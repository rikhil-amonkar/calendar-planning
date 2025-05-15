import z3

solver = z3.Solver()
S = z3.Int('S')

# Work hours: 9:00 (0) to 17:00 (480 minutes)
solver.add(S >= 0)
solver.add(S + 60 <= 480)

# James's blocked intervals (in minutes since 9:00)
james = [
    (150, 180),   # 11:30-12:00
    (330, 360)    # 14:30-15:00
]

# John's blocked intervals
john = [
    (30, 120),    # 9:30-11:00
    (150, 180),   # 11:30-12:00
    (210, 270),   # 12:30-13:30
    (330, 450)    # 14:30-16:30
]

# Combine all intervals from both participants
all_intervals = james + john

for start_block, end_block in all_intervals:
    solver.add(z3.Or(S + 60 <= start_block, S >= end_block))

if solver.check() == z3.sat:
    model = solver.model()
    start_minutes = model[S].as_long()
    # Convert to time strings
    start_h = 9 + start_minutes // 60
    start_m = start_minutes % 60
    end_minutes = start_minutes + 60
    end_h = 9 + end_minutes // 60
    end_m = end_minutes % 60
    print(f"Monday\n{start_h}:{start_m:02d}\n{end_h}:{end_m:02d}")
else:
    print("No solution found")