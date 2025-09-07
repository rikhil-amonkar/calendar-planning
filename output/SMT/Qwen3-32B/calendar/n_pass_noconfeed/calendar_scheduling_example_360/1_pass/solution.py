from z3 import *

def format_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

solver = Solver()

s = Int('s')

solver.add(s >= 540)  # 9:00 AM in minutes
solver.add(s + 30 <= 1020)  # 5:00 PM in minutes (end time must be <= 17:00)

# Emily's busy intervals: 10:00-10:30, 16:00-16:30
for a, b in [(600, 630), (960, 990)]:
    solver.add(Or(s + 30 <= a, s >= b))

# Maria's busy intervals: 10:30-11:00, 14:00-14:30
for a, b in [(630, 660), (840, 870)]:
    solver.add(Or(s + 30 <= a, s >= b))

# Carl's busy intervals: 9:30-10:00, 10:30-12:30, 13:30-14:00, 14:30-15:30, 16:00-17:00
for a, b in [(570, 600), (630, 750), (810, 840), (870, 930), (960, 1020)]:
    solver.add(Or(s + 30 <= a, s >= b))

# David's busy intervals: 9:30-11:00, 11:30-12:00, 12:30-13:30, 14:00-15:00, 16:00-17:00
for a, b in [(570, 660), (690, 720), (750, 810), (840, 900), (960, 1020)]:
    solver.add(Or(s + 30 <= a, s >= b))

# Frank's busy intervals: 9:30-10:30, 11:00-11:30, 12:30-13:30, 14:30-17:00
for a, b in [(570, 630), (660, 690), (750, 810), (870, 1020)]:
    solver.add(Or(s + 30 <= a, s >= b))

if solver.check() == sat:
    model = solver.model()
    start = model[s].as_long()
    end = start + 30
    start_str = format_time(start)
    end_str = format_time(end)
    print(f"Monday {start_str}:{end_str}")
else:
    print("No solution found")