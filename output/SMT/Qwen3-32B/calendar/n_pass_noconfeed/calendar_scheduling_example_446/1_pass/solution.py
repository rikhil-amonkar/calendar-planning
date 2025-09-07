from z3 import *

def minutes_to_time(m):
    hours = m // 60
    mins = m % 60
    return f"{hours:02d}:{mins:02d}"

solver = Solver()

S = Int('S')

# Work hours from 9:00 (540) to 17:00 (1020), meeting is 30 min
solver.add(S >= 540)
solver.add(S + 30 <= 1020)  # S <= 990

# Megan's busy intervals
megan = [(540, 570), (600, 660), (720, 750)]
for start, end in megan:
    solver.add(Or(S + 30 <= start, S >= end))

# Christine's
christine = [(540, 570), (690, 720), (780, 840), (930, 990)]
for start, end in christine:
    solver.add(Or(S + 30 <= start, S >= end))

# Sara's
sara = [(690, 720), (870, 900)]
for start, end in sara:
    solver.add(Or(S + 30 <= start, S >= end))

# Bruce's
bruce = [(570, 600), (630, 720), (750, 870), (870, 900), (930, 990)]
for start, end in bruce:
    solver.add(Or(S + 30 <= start, S >= end))

# Kathryn's
kathryn = [(600, 930), (960, 990)]
for start, end in kathryn:
    solver.add(Or(S + 30 <= start, S >= end))

# Billy's
billy = [(540, 570), (660, 690), (720, 840), (870, 930)]
for start, end in billy:
    solver.add(Or(S + 30 <= start, S >= end))

# Now check if solvable
if solver.check() == sat:
    model = solver.model()
    start_time = model[S].as_long()
    end_time = start_time + 30
    start_str = minutes_to_time(start_time)
    end_str = minutes_to_time(end_time)
    print(f"Monday {start_str}:{end_str}")
else:
    print("No solution found")