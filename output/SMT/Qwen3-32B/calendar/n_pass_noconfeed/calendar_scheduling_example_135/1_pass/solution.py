from z3 import *

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

s = Solver()

start = Int('start')

# Work hours: 9:00 (540) to 17:00 (1020)
s.add(start >= 540)
s.add(start + 30 <= 1020)  # end time is start + 30

# Ashley's busy intervals
ashley_busy = [
    (600, 630),  # 10:00-10:30
    (660, 720),  # 11:00-12:00
    (750, 780),  # 12:30-13:00
    (900, 960),  # 15:00-16:00
]
for b_start, b_end in ashley_busy:
    s.add(Or(start + 30 <= b_start, start >= b_end))

# Ronald's busy intervals
ronald_busy = [
    (540, 570),  # 9:00-9:30
    (600, 690),  # 10:00-11:30
    (750, 840),  # 12:30-14:00
    (870, 1020), # 14:30-17:00
]
for b_start, b_end in ronald_busy:
    s.add(Or(start + 30 <= b_start, start >= b_end))

# Larry's busy intervals
larry_busy = [
    (540, 720),   # 9:00-12:00
    (780, 1020),  # 13:00-17:00
]
for b_start, b_end in larry_busy:
    s.add(Or(start + 30 <= b_start, start >= b_end))

# Eric has no constraints

if s.check() == sat:
    m = s.model()
    start_time = m[start].as_long()
    end_time = start_time + 30
    start_str = minutes_to_time(start_time)
    end_str = minutes_to_time(end_time)
    print(f"Monday {start_str}:{end_str}")
else:
    print("No solution found")