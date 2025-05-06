from z3 import Solver, Int, Or, And, sat

s = Solver()
day = Int('day')
start = Int('start')

# Days: 0=Monday, 1=Tuesday (must choose Monday due to Doris's Tuesday schedule)
s.add(day == 0)
s.add(start >= 0, start + 30 <= 480)  # Total work hours 9:00-17:00

# Doris's Monday busy intervals (minutes since 9:00)
doris_busy = [(0, 150), (180, 210), (270, 420), (450, 480)]
for s_start, s_end in doris_busy:
    s.add(Or(start + 30 <= s_start, start >= s_end))

# Doris's preference: meeting ends before 14:00 (300 minutes since 9:00)
s.add(start + 30 <= 300)

# Jean has no Monday constraints (only busy on Tuesday)

# Find earliest possible time
s.minimize(start)

if s.check() == sat:
    m = s.model()
    start_time = m[start].as_long()
    hours = start_time // 60 + 9
    minutes = start_time % 60
    print(f"Meeting starts on Monday at {hours:02d}:{minutes:02d}")
else:
    print("No suitable time found.")