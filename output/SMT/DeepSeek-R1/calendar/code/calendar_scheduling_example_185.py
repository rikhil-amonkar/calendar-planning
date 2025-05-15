import z3

solver = z3.Optimize()
S = z3.Int('S')

# General time constraints (minutes since 9:00)
solver.add(S >= 60)          # Megan's preference: no meetings before 10:00
solver.add(S + 30 <= 480)    # Meeting must end by 17:00

# Define all blocked intervals in minutes
blocked_intervals = [
    # Kimberly's busy periods
    (60, 90), (120, 180), (420, 450),
    # Marie's busy periods
    (60, 120), (150, 360), (420, 450),
    # Diana's busy periods
    (30, 60), (90, 330), (390, 480)
]

# Add constraints to avoid all blocked intervals
for start, end in blocked_intervals:
    solver.add(z3.Or(S + 30 <= start, S >= end))

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