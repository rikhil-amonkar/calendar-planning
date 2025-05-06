from z3 import Solver, Int, Or, sat

s = Solver()
start = Int('start')

# Meeting duration 30 minutes, work hours 9:00-17:00 (480 minutes)
s.add(start >= 0, start <= 450)  # 450 = 17:00 - 0:30

# Judy's busy intervals (minutes since 9:00)
judy_busy = [(240, 270), (420, 450)]
for s_start, s_end in judy_busy:
    s.add(Or(start + 30 <= s_start, start >= s_end))

# Olivia's busy intervals
olivia_busy = [(60, 90), (180, 240), (300, 330)]
for s_start, s_end in olivia_busy:
    s.add(Or(start + 30 <= s_start, start >= s_end))

# Jacqueline's busy intervals
jacqueline_busy = [(60, 90), (360, 390)]
for s_start, s_end in jacqueline_busy:
    s.add(Or(start + 30 <= s_start, start >= s_end))

# Laura's busy intervals
laura_busy = [(0, 60), (90, 180), (240, 270), (330, 360), (390, 480)]
for s_start, s_end in laura_busy:
    s.add(Or(start + 30 <= s_start, start >= s_end))

# Tyler's busy intervals
tyler_busy = [(0, 60), (120, 150), (210, 240), (300, 330), (390, 480)]
for s_start, s_end in tyler_busy:
    s.add(Or(start + 30 <= s_start, start >= s_end))

# Lisa's busy intervals
lisa_busy = [(30, 90), (120, 150), (180, 210), (240, 270), (300, 330), (420, 480)]
for s_start, s_end in lisa_busy:
    s.add(Or(start + 30 <= s_start, start >= s_end))

# Eric has no constraints

# Find earliest possible time
s.minimize(start)

if s.check() == sat:
    m = s.model()
    start_min = m[start].as_long()
    hours = start_min // 60 + 9
    minutes = start_min % 60
    print(f"Meeting starts at {hours:02d}:{minutes:02d}")
else:
    print("No suitable time found.")