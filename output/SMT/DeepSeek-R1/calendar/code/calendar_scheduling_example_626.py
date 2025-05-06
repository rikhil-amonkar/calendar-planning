from z3 import *

s = Solver()
day = Int('day')
start = Int('start')

# Day must be 1 (Tuesday) since Jesse is busy all Monday
s.add(day == 1)

# Meeting duration constraints (1 hour within 9:00-17:00)
s.add(start >= 0, start + 60 <= 480)

# Patricia's Tuesday busy slots (minutes from 9:00)
patricia_busy = [
    (60, 90),    # 10:00-10:30
    (120, 180),  # 11:00-12:00
    (300, 420),  # 14:00-16:00
    (450, 480)   # 16:30-17:00
]
for (busy_start, busy_end) in patricia_busy:
    s.add(Or(start + 60 <= busy_start, start >= busy_end))

# Jesse's Tuesday busy slots
jesse_busy = [
    (120, 150),  # 11:00-11:30
    (180, 210),  # 12:00-12:30
    (240, 300),  # 13:00-14:00
    (330, 360),  # 14:30-15:00
    (390, 480)   # 15:30-17:00
]
for (busy_start, busy_end) in jesse_busy:
    s.add(Or(start + 60 <= busy_start, start >= busy_end))

if s.check() == sat:
    model = s.model()
    st = model[start].as_long()
    hours = 9 + st // 60
    minutes = st % 60
    print(f"Meeting can be scheduled on Tuesday at {hours:02d}:{minutes:02d}")
else:
    print("No valid time found.")