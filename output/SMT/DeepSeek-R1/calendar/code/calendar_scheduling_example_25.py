import z3

solver = z3.Optimize()
S = z3.Int('S')

# Work hours on Monday: 9:00 (0) to 17:00 (480 minutes)
solver.add(S >= 0)
solver.add(S + 60 <= 480)

# Pamela's constraint: meeting must end by 14:30 (330 minutes)
solver.add(S + 60 <= 330)

# Anthony's blocked intervals (minutes since 9:00)
anthony_blocks = [
    (30, 60),    # 9:30-10:00
    (180, 240),  # 12:00-13:00
    (420, 450)   # 16:00-16:30 (irrelevant due to Pamela's constraint)
]

# Pamela's blocked intervals
pamela_blocks = [
    (30, 60),    # 9:30-10:00
    (450, 480)   # 16:30-17:00 (irrelevant)
]

# Zachary's blocked intervals
zachary_blocks = [
    (0, 150),    # 9:00-11:30
    (180, 210),  # 12:00-12:30
    (240, 270),  # 13:00-13:30
    (330, 360),  # 14:30-15:00 (irrelevant due to Pamela's constraint)
    (420, 480)   # 16:00-17:00 (irrelevant)
]

# Add constraints for all blocked intervals
for start, end in anthony_blocks + pamela_blocks + zachary_blocks:
    solver.add(z3.Or(S >= end, S + 60 <= start))

# Find earliest possible time
solver.minimize(S)

if solver.check() == z3.sat:
    model = solver.model()
    start_minutes = model[S].as_long()
    start_h = 9 + start_minutes // 60
    start_m = start_minutes % 60
    end_minutes = start_minutes + 60
    end_h = 9 + end_minutes // 60
    end_m = end_minutes % 60
    print(f"Monday\n{start_h}:{start_m:02d}\n{end_h}:{end_m:02d}")
else:
    print("No solution found")