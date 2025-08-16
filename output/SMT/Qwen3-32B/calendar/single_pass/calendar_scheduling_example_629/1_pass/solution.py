from z3 import *

def to_time_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

solver = Solver()

start = Int('start')

# Constraints for Tuesday availability and Margaret's preference
solver.add(start >= 14 * 60 + 30)  # 14:30
solver.add(start + 30 <= 17 * 60)  # 17:00

# Avoid overlapping with Alexis's Tuesday blocked time (14:00-16:30)
solver.add(Or(start + 30 <= 14 * 60, start >= 16 * 60 + 30))

if solver.check() == sat:
    model = solver.model()
    start_val = model[start].as_long()
    day = "Tuesday"
    end_val = start_val + 30
    print("SOLUTION:")
    print(f"Day: {day}")
    print(f"Start Time: {to_time_str(start_val)}")
    print(f"End Time: {to_time_str(end_val)}")
else:
    print("No solution found")