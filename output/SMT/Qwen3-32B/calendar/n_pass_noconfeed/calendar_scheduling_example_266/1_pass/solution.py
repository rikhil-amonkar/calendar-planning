from z3 import *

def to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

solver = Solver()

start_time = Int('start_time')

# Work hours 9:00 (540) to 17:00 (1020). Meeting duration 30 mins.
solver.add(And(start_time >= 540, start_time <= 990))  # 990 +30 = 1020

# Joe's blocked: 9:30-10:00 (570-600), 10:30-11:00 (630-660)
for c, d in [(570, 600), (630, 660)]:
    solver.add(Or(start_time + 30 <= c, d <= start_time))

# Keith's blocked: 11:30-12:00 (690-720), 15:00-15:30 (900-930)
for c, d in [(690, 720), (900, 930)]:
    solver.add(Or(start_time + 30 <= c, d <= start_time))

# Patricia's blocked: 9:00-9:30 (540-570), 13:00-13:30 (780-810)
for c, d in [(540, 570), (780, 810)]:
    solver.add(Or(start_time + 30 <= c, d <= start_time))

# Nancy's blocked: 9:00-11:00 (540-660), 11:30-16:30 (690-990)
for c, d in [(540, 660), (690, 990)]:
    solver.add(Or(start_time + 30 <= c, d <= start_time))

# Pamela's blocked intervals in minutes
pam_blocked = [(540, 600), (630, 660), (690, 750), (780, 840), (870, 900), (930, 960), (990, 1020)]
for c, d in pam_blocked:
    solver.add(Or(start_time + 30 <= c, d <= start_time))

if solver.check() == sat:
    model = solver.model()
    st = model[start_time].as_long()
    start_str = to_time(st)
    end_str = to_time(st + 30)
    print(f"{{{start_str}:{end_str}}} Monday")
else:
    print("No solution found.")