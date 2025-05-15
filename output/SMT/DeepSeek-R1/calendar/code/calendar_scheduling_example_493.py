import z3

solver = z3.Optimize()
S = z3.Int('S')

# Total work hours on Monday: 9:00 (0) to 17:00 (480 minutes)
solver.add(S >= 0)
solver.add(S + 30 <= 480)

# Define blocked intervals in minutes since 9:00
blocked_intervals = [
    # Stephanie's blocks
    (120, 150), (330, 360),
    # Joe's blocks
    (0, 30), (60, 180), (210, 240), (300, 480),
    # Diana's blocks
    (0, 90), (150, 180), (240, 300), (330, 390), (420, 480),
    # Deborah's blocks
    (0, 60), (90, 180), (210, 240), (270, 300), (330, 390), (420, 450)
]

# Add constraints that meeting doesn't overlap with any blocked time
for start, end in blocked_intervals:
    solver.add(z3.Or(S + 30 <= start, S >= end))

# Find earliest possible meeting time
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