from z3 import *

def minutes_to_time(m):
    hours = m // 60
    mins = m % 60
    return f"{hours:02d}:{mins:02d}"

solver = Solver()
start_time = Int('start_time')

# Constraints for Tuesday after 14:30 (870 minutes) and before 17:00 (1020 minutes)
solver.add(And(start_time >= 870, start_time <= 990))

# Alexis's blocked intervals on Tuesday
blocked_intervals_alex_tuesday = [
    (540, 570),  # 9:00-9:30
    (600, 630),  # 10:00-10:30
    (840, 990)   # 14:00-16:30
]

for start_blocked, end_blocked in blocked_intervals_alex_tuesday:
    solver.add(Or(start_time + 30 <= start_blocked, end_blocked <= start_time))

if solver.check() == sat:
    model = solver.model()
    start = model[start_time].as_long()
    end = start + 30
    day = "Tuesday"
    time_str = f"{minutes_to_time(start)}:{minutes_to_time(end)}"
    print(f"{day} {time_str}")
else:
    print("No solution found")