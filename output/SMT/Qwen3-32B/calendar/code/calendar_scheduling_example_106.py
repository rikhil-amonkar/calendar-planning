from z3 import *

# Define the start time variable
start_time = Int('start_time')

# Create a solver instance
s = Solver()

# Olivia's blocked intervals
s.add(Or(start_time + 60 <= 180, start_time >= 210))  # 12:30–13:30
s.add(Or(start_time + 60 <= 330, start_time >= 360))  # 14:30–15:00
s.add(Or(start_time + 60 <= 390, start_time >= 420))  # 16:30–17:00

# Virginia's blocked intervals
s.add(Or(start_time + 60 <= 0, start_time >= 60))     # 9:00–10:00
s.add(Or(start_time + 60 <= 150, start_time >= 300))  # 11:30–16:00
s.add(Or(start_time + 60 <= 390, start_time >= 420))  # 16:30–17:00

# Paul's blocked intervals
s.add(Or(start_time + 60 <= 0, start_time >= 30))     # 9:00–9:30
s.add(Or(start_time + 60 <= 120, start_time >= 150))  # 11:00–11:30
s.add(Or(start_time + 60 <= 240, start_time >= 300))  # 13:00–14:00
s.add(Or(start_time + 60 <= 330, start_time >= 360))  # 14:30–16:00
s.add(Or(start_time + 60 <= 390, start_time >= 420))  # 16:30–17:00

# Meeting duration and time bounds
s.add(And(start_time >= 0, start_time + 60 <= 450))

# Solve and print the result
if s.check() == sat:
    m = s.model()
    print(f"Start time: {m[start_time]} minutes")
else:
    print("No solution")