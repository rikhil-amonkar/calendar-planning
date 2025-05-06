from z3 import *

# Define the start time variable
start_time = Int('start_time')

# Create a solver instance
s = Solver()

# Nicole's blocked intervals on Wednesday
s.add(Or(start_time + 30 <= 60, start_time >= 120))  # 10:00–11:00
s.add(Or(start_time + 30 <= 180, start_time >= 300))  # 12:30–15:00
s.add(Or(start_time + 30 <= 360, start_time >= 420))  # 16:00–17:00

# Ruth's blocked intervals on Wednesday
s.add(Or(start_time + 30 <= 0, start_time >= 90))     # 9:00–10:30
s.add(Or(start_time + 30 <= 120, start_time >= 150))  # 11:00–11:30
s.add(Or(start_time + 30 <= 180, start_time >= 210))  # 12:00–12:30
s.add(Or(start_time + 30 <= 270, start_time >= 390))  # 13:30–15:30
s.add(Or(start_time + 30 <= 360, start_time >= 390))  # 16:00–16:30

# Ruth's preference: meeting must be before 13:30 (270 minutes)
s.add(start_time < 270)

# Meeting duration is 30 minutes
s.add(And(start_time >= 0, start_time + 30 <= 450))

# Solve and print the result
if s.check() == sat:
    m = s.model()
    print(f"Start time: {m[start_time]} minutes")
else:
    print("No solution")