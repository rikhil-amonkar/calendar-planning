from z3 import *

s = Optimize()
start = Int('start')
s.add(start >= 0)
s.add(start + 30 <= 480)  # Meeting must end by 17:00 (480 minutes)

# Define each participant's busy time intervals in minutes (relative to 9:00)
lisa_busy = [(0, 30), (90, 120), (300, 420)]
anthony_busy = [(0, 30), (120, 150), (210, 240), (300, 360), (390, 420), (450, 480)]

# Add constraints to avoid overlapping with busy times
for (busy_start, busy_end) in lisa_busy + anthony_busy:
    s.add(Or(start + 30 <= busy_start, start >= busy_end))

# Find the earliest possible start time by minimizing the variable
s.minimize(start)

if s.check() == sat:
    model = s.model()
    start_time = model[start].as_long()
    hours = 9 + start_time // 60
    minutes = start_time % 60
    print(f"Meeting can be scheduled at {hours:02d}:{minutes:02d}")
else:
    print("No valid time found.")