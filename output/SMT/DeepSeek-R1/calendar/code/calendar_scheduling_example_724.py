import z3

solver = z3.Optimize()
day = z3.Int('day')
S = z3.Int('S')

# Day must be Monday (0)
solver.add(day == 0)

# Time constraints (minutes since 9:00)
solver.add(S >= 420)          # Tyler's preference: no meetings before 16:00 (420 minutes)
solver.add(S + 30 <= 450)     # Ruth's last available slot ends at 16:30 (450 minutes)

# Ruth's blocked intervals on Monday (converted to minutes)
ruth_blocked = [
    (0, 60),    # 9:00-10:00
    (90, 180),  # 10:30-12:00
    (210, 330), # 12:30-14:30
    (360, 420), # 15:00-16:00
    (450, 480)  # 16:30-17:00
]

# Ensure meeting doesn't overlap with Ruth's blocked times
for start, end in ruth_blocked:
    solver.add(z3.Or(S + 30 <= start, S >= end))

# Find earliest possible time
solver.minimize(S)

if solver.check() == z3.sat:
    model = solver.model()
    d = model[day].as_long()
    s = model[S].as_long()
    days = ["Monday", "Tuesday", "Wednesday"]
    start_h = 9 + s // 60
    start_m = s % 60
    end_h = 9 + (s + 30) // 60
    end_m = (s + 30) % 60
    print(f"{days[d]}\n{start_h}:{start_m:02d}\n{end_h}:{end_m:02d}")
else:
    print("No solution found")