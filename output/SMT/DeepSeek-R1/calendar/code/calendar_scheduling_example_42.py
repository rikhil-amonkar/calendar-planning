from z3 import Solver, Int, Or, sat

solver = Solver()
S = Int('S')

# Meeting must be within 9:00 to 17:00 (480 minutes)
solver.add(S >= 0)
solver.add(S + 60 <= 480)

# Julie's blocked times (minutes since 9:00)
julie_blocks = [(0, 30), (120, 150), (180, 210), (270, 300), (420, 480)]
for start, end in julie_blocks:
    solver.add(Or(S + 60 <= start, S >= end))

# Sean's blocked times
sean_blocks = [(0, 30), (240, 270), (360, 390), (420, 450)]
for start, end in sean_blocks:
    solver.add(Or(S + 60 <= start, S >= end))

# Lori's blocked times
lori_blocks = [(60, 90), (120, 240), (390, 480)]
for start, end in lori_blocks:
    solver.add(Or(S + 60 <= start, S >= end))

if solver.check() == sat:
    model = solver.model()
    start_min = model[S].as_long()
    # Convert to time strings
    start_h = 9 + start_min // 60
    start_m = start_min % 60
    end_min = start_min + 60
    end_h = 9 + end_min // 60
    end_m = end_min % 60
    print(f"Monday {start_h:02d}:{start_m:02d}-{end_h:02d}:{end_m:02d}")
else:
    print("No solution found")