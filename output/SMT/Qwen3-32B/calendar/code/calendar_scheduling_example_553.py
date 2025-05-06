from z3 import *

start_time = Int('start_time')
s = Solver()

# Eric's blocked intervals
s.add(Or(start_time + 30 <= 180, start_time >= 210))  # 12:00-13:00
s.add(Or(start_time + 30 <= 300, start_time >= 330))  # 14:00-15:00

# Henry's blocked intervals before 10:00
s.add(Or(start_time + 30 <= 30, start_time >= 60))  # 9:30-10:00

# Henry's preference: meeting before or at 10:00
s.add(start_time <= 60)

# Meeting duration and time bounds
s.add(And(start_time >= 0, start_time + 30 <= 450))

if s.check() == sat:
    m = s.model()
    print(f"Start time: {m[start_time]} minutes")
else:
    print("No solution")