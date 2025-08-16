from z3 import *

solver = Solver()

s = Int('s')

# Work hours are from 9:00 (540 minutes) to 17:00 (1020 minutes)
solver.add(And(s >= 540, s <= 990))  # 990 = 16:30, meeting ends at 17:00

# Kimberly's busy intervals (in minutes since midnight)
kim_busy = [(600, 630), (660, 720), (960, 990)]
for b_start, b_end in kim_busy:
    solver.add(Or(s + 30 <= b_start, s >= b_end))

# Marie's busy intervals
marie_busy = [(600, 660), (690, 900), (960, 990)]
for b_start, b_end in marie_busy:
    solver.add(Or(s + 30 <= b_start, s >= b_end))

# Diana's busy intervals
diana_busy = [(570, 600), (630, 870), (930, 1020)]
for b_start, b_end in diana_busy:
    solver.add(Or(s + 30 <= b_start, s >= b_end))

# Megan's preference: avoid before 10:00 (600 minutes)
solver.add(s >= 600)

if solver.check() == sat:
    model = solver.model()
    start = model[s].as_long()
    end = start + 30

    def to_time(mins):
        hours = mins // 60
        mins_remaining = mins % 60
        return f"{hours:02d}:{mins_remaining:02d}"

    print("SOLUTION:")
    print(f"Day: Monday")
    print(f"Start Time: {to_time(start)}")
    print(f"End Time: {to_time(end)}")
else:
    print("No solution found.")