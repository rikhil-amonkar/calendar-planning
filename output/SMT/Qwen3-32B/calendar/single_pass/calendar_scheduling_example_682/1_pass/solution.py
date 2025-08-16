from z3 import *

# Define the busy periods in minutes since midnight
amanda_tuesday = [
    (540, 570),  # 9:00-9:30
    (600, 630),  # 10:00-10:30
    (690, 720),  # 11:30-12:00
    (810, 870),  # 13:30-14:30
    (930, 960),  # 15:30-16:00
    (990, 1020)  # 16:30-17:00
]

nathan_tuesday = [
    (540, 630),  # 9:00-10:30
    (660, 780),  # 11:00-13:00
    (810, 840),  # 13:30-14:00
    (870, 930),  # 14:30-15:30
    (960, 990)   # 16:00-16:30
]

solver = Solver()
s = Int('s')

# Constraints for the start time on Tuesday between 9:00 and 11:00
solver.add(s >= 540)
solver.add(s <= 630)

# Add constraints for Amanda's busy periods
for b_start, b_end in amanda_tuesday:
    solver.add(Or(s >= b_end, s + 30 <= b_start))

# Add constraints for Nathan's busy periods
for b_start, b_end in nathan_tuesday:
    solver.add(Or(s >= b_end, s + 30 <= b_start))

if solver.check() == sat:
    model = solver.model()
    s_val = model[s].as_long()
    start_h = s_val // 60
    start_m = s_val % 60
    end_h = (s_val + 30) // 60
    end_m = (s_val + 30) % 60
    start_time = f"{start_h:02d}:{start_m:02d}"
    end_time = f"{end_h:02d}:{end_m:02d}"
    print("SOLUTION:")
    print(f"Day: Tuesday")
    print(f"Start Time: {start_time}")
    print(f"End Time: {end_time}")
else:
    print("No solution found.")