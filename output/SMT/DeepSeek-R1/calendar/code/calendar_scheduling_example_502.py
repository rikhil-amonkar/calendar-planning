import z3

solver = z3.Solver()
S = z3.Int('S')

# Work hours: 9:00 (0) to 17:00 (480 minutes)
solver.add(S >= 0)
solver.add(S + 30 <= 480)

# Jack's constraints: meeting must end by 12:30 (210 minutes from 9:00)
solver.add(S + 30 <= 210)

# Jack's blocked intervals (minutes since 9:00)
jack_blocks = [
    (30, 90),    # 9:30-10:30
    (120, 150),  # 11:00-11:30
    (210, 240),  # 12:30-13:00 (irrelevant due to preference)
    (300, 330),  # 14:00-14:30 (irrelevant)
    (420, 450)   # 16:00-16:30 (irrelevant)
]

# Charlotte's blocked intervals (minutes since 9:00)
charlotte_blocks = [
    (30, 60),    # 9:30-10:00
    (90, 180),   # 10:30-12:00
    (210, 270),  # 12:30-13:30 (irrelevant)
    (300, 420)   # 14:00-16:00 (irrelevant)
]

# Add constraints for all blocked intervals (relevant ones enforced via S constraints)
for start, end in jack_blocks + charlotte_blocks:
    solver.add(z3.Or(S + 30 <= start, S >= end))

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