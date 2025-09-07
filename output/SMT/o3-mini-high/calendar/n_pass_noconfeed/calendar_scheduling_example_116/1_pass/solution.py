from z3 import *

def minutes_to_time(mins):
    hours = mins // 60
    minutes = mins % 60
    return f"{hours:02}:{minutes:02}"

# Meeting duration in minutes
duration = 30

# Create a solver instance
solver = Solver()

# Define meeting start time variable (in minutes since midnight)
# Working hours: 9:00 (540) to 17:00 (1020), so meeting must start no later than 1020 - 30 = 990.
x = Int('x')
solver.add(x >= 540, x <= 990)

# Anna prefers no meeting before 14:30 (870 minutes)
solver.add(x >= 870)

# Adam is busy from 14:00 to 15:00 ([840, 900])
solver.add(Or(x + duration <= 840, x >= 900))

# John's busy intervals:
# 13:00 to 13:30 -> [780, 810]
solver.add(Or(x + duration <= 780, x >= 810))
# 14:00 to 14:30 -> [840, 870]
solver.add(Or(x + duration <= 840, x >= 870))
# 15:30 to 16:00 -> [930, 960]
solver.add(Or(x + duration <= 930, x >= 960))
# 16:30 to 17:00 -> [990, 1020]
solver.add(Or(x + duration <= 990, x >= 1020))

# Stephanie's busy intervals:
# 9:30 to 10:00 -> [570, 600]
solver.add(Or(x + duration <= 570, x >= 600))
# 10:30 to 11:00 -> [630, 660]
solver.add(Or(x + duration <= 630, x >= 660))
# 11:30 to 16:00 -> [690, 960]
solver.add(Or(x + duration <= 690, x >= 960))
# 16:30 to 17:00 -> [990, 1020]
solver.add(Or(x + duration <= 990, x >= 1020))

# Anna's busy intervals:
# 9:30 to 10:00 -> [570, 600]
solver.add(Or(x + duration <= 570, x >= 600))
# 12:00 to 12:30 -> [720, 750]
solver.add(Or(x + duration <= 720, x >= 750))
# 13:00 to 15:30 -> [780, 930]
solver.add(Or(x + duration <= 780, x >= 930))
# 16:30 to 17:00 -> [990, 1020]
solver.add(Or(x + duration <= 990, x >= 1020))

# Check for a solution
if solver.check() == sat:
    model = solver.model()
    start = model[x].as_long()
    end = start + duration
    # Output the day and time range in HH:MM:HH:MM format.
    print("Monday")
    print(f"{minutes_to_time(start)}:{minutes_to_time(end)}")
else:
    print("No solution found")