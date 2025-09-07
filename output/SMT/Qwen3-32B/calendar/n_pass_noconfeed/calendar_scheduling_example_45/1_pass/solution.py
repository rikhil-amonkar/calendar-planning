from z3 import *

def to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

# Define the start time variable
start_time = Int('start_time')

# Initialize the optimizer
opt = Optimize()

# Add constraints for work hours (9:00 to 17:00, 540 to 1020 minutes)
opt.add(start_time >= 540)
opt.add(start_time + 30 <= 1020)

# Samuel's blocked intervals in minutes since midnight
blocked_intervals = [
    (540, 630),   # 9:00-10:30
    (690, 720),   # 11:30-12:00
    (780, 810),   # 13:00-13:30
    (840, 960),   # 14:00-16:00
    (990, 1020)   # 16:30-17:00
]

# Add constraints to avoid blocked intervals
for s_start, s_end in blocked_intervals:
    opt.add(Or(start_time + 30 <= s_start, start_time >= s_end))

# Minimize the start time
opt.minimize(start_time)

# Check for a solution
if opt.check() == sat:
    model = opt.model()
    start = model[start_time].as_long()
    end = start + 30
    time_range = f"{to_time(start)}:{to_time(end)}"
    day = "Monday"
    print(f"{time_range} {day}")
else:
    print("No solution found.")