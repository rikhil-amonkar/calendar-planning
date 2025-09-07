from z3 import *

def to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

start = Int('start')
s = Solver()

# Work hours: 9:00 (540) to 17:00 (1020)
s.add(start >= 540)
s.add(start + 30 <= 1020)

# Busy intervals for all participants except Tyler, Kelly, Hannah
busy_intervals = [
    # Stephanie
    (660, 690),
    (870, 900),
    # Joe
    (540, 570),
    (600, 720),
    (750, 780),
    (840, 1020),
    # Diana
    (540, 630),
    (690, 720),
    (780, 840),
    (870, 930),
    (960, 1020),
    # Deborah
    (540, 600),
    (630, 720),
    (750, 780),
    (810, 840),
    (870, 930),
    (960, 990),
]

for b_start, b_end in busy_intervals:
    s.add(Or(start + 30 <= b_start, start >= b_end))

if s.check() == sat:
    model = s.model()
    start_val = model[start].as_long()
    end_val = start_val + 30
    start_time = to_time(start_val)
    end_time = to_time(end_val)
    print(f"{{{start_time}:{end_time}}} Monday")
else:
    print("No solution found")