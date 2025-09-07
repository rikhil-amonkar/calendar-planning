from z3 import *

def to_minutes(h, m):
    return h * 60 + m

busy_intervals = []

# Joshua's busy intervals
busy_intervals.extend([
    (to_minutes(11, 0), to_minutes(12, 30)),
    (to_minutes(13, 30), to_minutes(14, 30)),
    (to_minutes(16, 30), to_minutes(17, 0))
])

# Jerry's busy intervals
busy_intervals.extend([
    (to_minutes(9, 0), to_minutes(9, 30)),
    (to_minutes(10, 30), to_minutes(12, 0)),
    (to_minutes(12, 30), to_minutes(13, 0)),
    (to_minutes(13, 30), to_minutes(14, 0)),
    (to_minutes(14, 30), to_minutes(15, 0)),
    (to_minutes(15, 30), to_minutes(16, 0))
])

# Jesse's busy intervals
busy_intervals.extend([
    (to_minutes(9, 0), to_minutes(9, 30)),
    (to_minutes(10, 30), to_minutes(12, 0)),
    (to_minutes(12, 30), to_minutes(13, 0)),
    (to_minutes(14, 30), to_minutes(15, 0)),
    (to_minutes(15, 30), to_minutes(16, 30))
])

# Kenneth's busy intervals
busy_intervals.extend([
    (to_minutes(10, 30), to_minutes(12, 30)),
    (to_minutes(13, 30), to_minutes(14, 0)),
    (to_minutes(14, 30), to_minutes(15, 0)),
    (to_minutes(15, 30), to_minutes(16, 0)),
    (to_minutes(16, 30), to_minutes(17, 0))
])

s = Solver()
start = Int('start')

# Meeting must be between 9:00 and 17:00 (start + 60 <= 17:00 => start <= 16:00)
s.add(start >= to_minutes(9, 0))
s.add(start <= to_minutes(16, 0))

for b_start, b_end in busy_intervals:
    s.add(Or(start + 60 <= b_start, start >= b_end))

if s.check() == sat:
    m = s.model()
    start_time = m[start].as_long()
    start_h = start_time // 60
    start_m = start_time % 60
    end_time = start_time + 60
    end_h = end_time // 60
    end_m = end_time % 60

    def format_time(h, m):
        return f"{h:02d}:{m:02d}"

    start_str = format_time(start_h, start_m)
    end_str = format_time(end_h, end_m)
    print(f"{start_str}:{end_str} Monday")
else:
    print("No solution found.")