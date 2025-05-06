from z3 import *

s = Solver()
start = Int('start')

# General constraints: 1 hour between 9:00 (0) and 17:00 (480)
s.add(start >= 0)
s.add(start + 60 <= 480)

# Joshua's busy slots (11:00-12:30, 13:30-14:30, 16:30-17:00)
s.add(Or(start + 60 <= 120, start >= 210))  # 11:00-12:30
s.add(Or(start + 60 <= 270, start >= 330))  # 13:30-14:30
s.add(Or(start + 60 <= 450, start >= 480))  # 16:30-17:00

# Jerry's busy slots
busy_jerry = [(0, 30), (90, 180), (210, 240), (270, 300), (330, 360), (390, 420)]
for (b_start, b_end) in busy_jerry:
    s.add(Or(start + 60 <= b_start, start >= b_end))

# Jesse's busy slots
busy_jesse = [(0, 30), (90, 180), (210, 240), (330, 360), (390, 450)]
for (b_start, b_end) in busy_jesse:
    s.add(Or(start + 60 <= b_start, start >= b_end))

# Kenneth's busy slots
busy_kenneth = [(90, 210), (270, 300), (330, 360), (390, 420), (450, 480)]
for (b_start, b_end) in busy_kenneth:
    s.add(Or(start + 60 <= b_start, start >= b_end))

if s.check() == sat:
    model = s.model()
    st = model[start].as_long()
    hours = 9 + st // 60
    minutes = st % 60
    print(f"Meeting can be scheduled on Monday at {hours:02d}:{minutes:02d}")
else:
    print("No valid time found.")