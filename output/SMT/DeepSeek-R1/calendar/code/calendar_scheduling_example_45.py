from z3 import Optimize, Int, Or, sat

s = Optimize()
start = Int('start')

# Meeting duration is 30 minutes, work hours 9:00-17:00 (480 minutes)
s.add(start >= 0, start <= 450)  # 450 = 17:00 - 0:30

# Samuel's busy intervals (converted to minutes since 9:00)
samuel_busy = [
    (0, 90),     # 9:00-10:30
    (150, 180),  # 11:30-12:00
    (240, 270),  # 13:00-13:30
    (300, 420),  # 14:00-16:00
    (450, 480)   # 16:30-17:00
]

# Add constraints for Samuel's availability
for s_start, s_end in samuel_busy:
    s.add(Or(start + 30 <= s_start, start >= s_end))

# Andrew and Grace have no constraints, so no additional rules needed

# Find earliest possible time by minimizing start
s.minimize(start)

if s.check() == sat:
    m = s.model()
    start_min = m[start].as_long()
    hours = start_min // 60 + 9
    minutes = start_min % 60
    print(f"Meeting starts at {hours:02d}:{minutes:02d}")
else:
    print("No suitable time found.")