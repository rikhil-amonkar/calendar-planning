import z3

solver = z3.Optimize()
S = z3.Int('S')

# Total work hours on Monday: 9:00 (0) to 17:00 (480 minutes)
solver.add(S >= 0)
solver.add(S + 30 <= 480)

# Define all blocked intervals in minutes since 9:00
blocked_intervals = [
    # Megan's blocks
    (0, 30), (60, 120), (180, 210),
    # Christine's blocks
    (0, 30), (150, 180), (240, 300), (390, 420),
    # Sara's blocks
    (150, 180), (330, 360),
    # Bruce's blocks
    (30, 60), (90, 180), (210, 300), (330, 360), (390, 420),
    # Kathryn's blocks
    (60, 330), (420, 450),
    # Billy's blocks
    (0, 30), (120, 150), (180, 300), (330, 390)
]

# Add constraints to avoid all blocked intervals
for start, end in blocked_intervals:
    solver.add(z3.Or(S + 30 <= start, S >= end))

# Find the earliest possible time
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