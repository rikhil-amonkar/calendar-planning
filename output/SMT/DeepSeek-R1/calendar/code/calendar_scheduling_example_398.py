import z3

solver = z3.Solver()
S = z3.Int('S')

# Work hours: 9:00 (0) to 17:00 (480 minutes)
solver.add(S >= 0)
solver.add(S + 30 <= 480)

# Define blocked intervals for each participant (in minutes since 9:00)
participants = [
    # Doris
    [(0, 120), (270, 300), (420, 450)],
    # Theresa
    [(60, 180)],
    # Christian (no blocks)
    [],
    # Terry
    [(30, 60), (150, 180), (210, 240), (270, 300), (330, 360), (390, 480)],
    # Carolyn
    [(0, 90), (120, 150), (180, 240), (270, 330), (360, 480)],
    # Kyle
    [(0, 30), (150, 180), (210, 240), (330, 480)]
]

# Add constraints for all blocked intervals
for person in participants:
    for start_block, end_block in person:
        solver.add(z3.Or(S + 30 <= start_block, S >= end_block))

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