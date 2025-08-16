from z3 import *

solver = Solver()
start = Int('start')

# Evelyn's constraints: meeting starts between 9:00 and 12:30 (inclusive)
solver.add(start >= 9 * 60)
solver.add(start <= 12 * 60 + 30)

# Randy's blocked intervals
blocked_randy = [
    (9 * 60, 10 * 60 + 30),  # 9:00-10:30
    (11 * 60, 15 * 60 + 30), # 11:00-15:30
    (16 * 60, 17 * 60)       # 16:00-17:00
]

# Ensure no overlap with Randy's blocked intervals
for b_start, b_end in blocked_randy:
    end = start + 30
    solver.add(Or(end <= b_start, start >= b_end))

if solver.check() == sat:
    model = solver.model()
    start_val = model[start].as_long()
    end_val = start_val + 30
    day = "Monday"
    start_time = f"{start_val // 60:02d}:{start_val % 60:02d}"
    end_time = f"{end_val // 60:02d}:{end_val % 60:02d}"
    print("SOLUTION:")
    print(f"Day: {day}")
    print(f"Start Time: {start_time}")
    print(f"End Time: {end_time}")
else:
    print("No solution found")