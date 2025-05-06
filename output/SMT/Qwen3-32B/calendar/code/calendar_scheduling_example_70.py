from z3 import *

# Define the start time variable
start_time = Int('start_time')

# Create a solver instance
s = Solver()

# Denise's blocked intervals
s.add(Or(start_time + 30 <= 180, start_time >= 210))  # 12:00–12:30
s.add(Or(start_time + 30 <= 330, start_time >= 360))  # 15:30–16:00

# Natalie's blocked intervals
s.add(Or(start_time + 30 <= 0, start_time >= 150))    # 9:00–11:30
s.add(Or(start_time + 30 <= 180, start_time >= 240))  # 12:00–13:00
s.add(Or(start_time + 30 <= 300, start_time >= 330))  # 14:00–14:30
s.add(Or(start_time + 30 <= 300, start_time >= 420))  # 15:00–17:00

# Meeting duration and time bounds
s.add(And(start_time >= 0, start_time + 30 <= 450))

# Solve and print the result
if s.check() == sat:
    m = s.model()
    print(f"Start time: {m[start_time]} minutes")
else:
    print("No solution")