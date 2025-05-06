from z3 import *

# Define the start time variable
start_time = Int('start_time')

# Define the constraints
s = Solver()

# Work hours: 9:00 to 17:00 (0 to 420 minutes)
s.add(0 <= start_time, start_time + 30 <= 420)

# Doris's blocked intervals on Monday
# 9:00–11:30 (0–150)
s.add(Or(start_time + 30 <= 0, start_time >= 150))

# 12:00–12:30 (180–210)
s.add(Or(start_time + 30 <= 180, start_time >= 210))

# Doris prefers not to meet after 14:00 (240 minutes)
s.add(start_time < 240)

# Check for a solution
if s.check() == sat:
    model = s.model()
    start_minutes = model[start_time].as_long()
    start_time_str = f"{9 + start_minutes // 60}:{start_minutes % 60:02d}"
    end_time_str = f"{9 + (start_minutes + 30) // 60}:{(start_minutes + 30) % 60:02d}"
    print(f"Meeting can be scheduled from {start_time_str} to {end_time_str}")
else:
    print("No valid time found.")