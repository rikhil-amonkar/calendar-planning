import z3

solver = z3.Optimize()
S = z3.Int('S')

# Total work hours on Monday: 9:00 (0) to 17:00 (480 minutes)
solver.add(S >= 0)
solver.add(S + 30 <= 480)

# Nicole's blocked intervals (minutes since 9:00)
nicole_blocks = [
    (0, 60),   # 9:00-10:00
    (90, 450)  # 10:30-16:30
]

# Add constraints to avoid blocked intervals
for start, end in nicole_blocks:
    solver.add(z3.Or(S + 30 <= start, S >= end))

# Nicole's preference: meeting starts at or after 16:00 (420 minutes)
solver.add(S >= 420)

# Find earliest possible time
solver.minimize(S)

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