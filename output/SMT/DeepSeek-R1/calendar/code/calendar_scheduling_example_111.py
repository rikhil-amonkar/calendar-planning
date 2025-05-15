from z3 import Solver, Int, Or, sat

solver = Solver()
S = Int('S')

# Meeting must be within 9:00 to 17:00 (480 minutes)
solver.add(S >= 0)
solver.add(S + 30 <= 480)

# Gregory's blocked times (in minutes since 9:00)
gregory_blocks = [(0, 60), (90, 150), (210, 240), (270, 300)]
for start, end in gregory_blocks:
    solver.add(Or(S + 30 <= start, S >= end))

# Christine's blocked times
christine_blocks = [(0, 150), (270, 480)]
for start, end in christine_blocks:
    solver.add(Or(S + 30 <= start, S >= end))

# Vincent's blocked times
vincent_blocks = [(0, 30), (90, 180), (210, 300), (330, 480)]
for start, end in vincent_blocks:
    solver.add(Or(S + 30 <= start, S >= end))

# Natalie has no blocks, so no constraints

if solver.check() == sat:
    model = solver.model()
    start_min = model[S].as_long()
    # Convert to time strings
    start_h = 9 + start_min // 60
    start_m = start_min % 60
    end_min = start_min + 30
    end_h = 9 + end_min // 60
    end_m = end_min % 60
    print(f"Monday {start_h:02d}:{start_m:02d}-{end_h:02d}:{end_m:02d}")
else:
    print("No solution found")