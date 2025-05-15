import z3

solver = z3.Solver()
S = z3.Int('S')

# Work hours: 9:00 (0) to 17:00 (480 minutes)
solver.add(S >= 0)
solver.add(S + 30 <= 480)

# Albert's blocked intervals (in minutes since 9:00)
albert = [
    (0, 60),     # 9:00-10:00
    (90, 180),   # 10:30-12:00
    (360, 450)   # 15:00-16:30
]

# Albert can't meet after 11:00 (120 minutes from 9:00)
solver.add(S + 30 <= 120)

# Add constraints for Albert's blocked times
for start_block, end_block in albert:
    solver.add(z3.Or(S + 30 <= start_block, S >= end_block))

# Deborah is free, no constraints needed

if solver.check() == z3.sat:
    model = solver.model()
    start_minutes = model[S].as_long()
    start_h = 9 + start_minutes // 60
    start_m = start_minutes % 60
    end_minutes = start_minutes + 30
    end_h = 9 + end_minutes // 60
    end_m = end_minutes % 60
    print(f"Monday\n{start_h}:{start_m:02d}\n{end_h}:{end_m:02d}")
else:
    print("No solution found")