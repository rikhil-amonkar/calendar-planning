from z3 import *

solver = Solver()

start_time = Int('start_time')

# Constraints for the meeting to be between 9:00 (540) and 12:30 (750) due to Harold's preference
solver.add(start_time >= 540)
solver.add(start_time <= 750)

# Busy intervals for each participant converted to minutes since midnight
busy_jac = [(540, 570), (660, 690), (750, 780), (930, 960)]
busy_harold = [(600, 630), (780, 810), (900, 1020)]
busy_arthur = [(540, 570), (600, 750), (870, 900), (930, 1020)]
busy_kelly = [(540, 570), (600, 660), (690, 750), (840, 900), (930, 960)]

# Combine all busy intervals
all_busy = busy_jac + busy_harold + busy_arthur + busy_kelly

# Add constraints to ensure no overlap with any busy intervals
for b_start, b_end in all_busy:
    solver.add(Or(start_time >= b_end, start_time + 30 <= b_start))

if solver.check() == sat:
    model = solver.model()
    start = model[start_time].as_long()
    end = start + 30

    def to_time(m):
        hours = m // 60
        minutes = m % 60
        return f"{hours:02d}:{minutes:02d}"

    day = "Monday"
    print(f"SOLUTION:")
    print(f"Day: {day}")
    print(f"Start Time: {to_time(start)}")
    print(f"End Time: {to_time(end)}")
else:
    print("No solution found.")