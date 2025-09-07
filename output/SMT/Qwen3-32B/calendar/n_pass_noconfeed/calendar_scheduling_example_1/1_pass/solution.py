from z3 import *

def to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

s = Solver()

S = Int('S')

# Work hours from 9:00 (540) to 17:00 (1020)
s.add(S >= 540)
s.add(S <= 990)  # S + 30 <= 1020 → S <= 990

# Raymond's blocked intervals
raymond_blocked = [
    (540, 570),  # 9:00-9:30
    (690, 720),  # 11:30-12:00
    (780, 810),  # 13:00-13:30
    (900, 930),  # 15:00-15:30
]

for a, b in raymond_blocked:
    s.add(Or(S + 30 <= a, S >= b))

# Billy's blocked intervals
billy_blocked = [
    (600, 630),  # 10:00-10:30
    (720, 780),  # 12:00-13:00
    (990, 1020), # 16:30-17:00
]

for a, b in billy_blocked:
    s.add(Or(S + 30 <= a, S >= b))

# Donald's blocked intervals
donald_blocked = [
    (540, 570),  # 9:00-9:30
    (600, 660),  # 10:00-11:00
    (720, 780),  # 12:00-13:00
    (840, 870),  # 14:00-14:30
    (960, 1020), # 16:00-17:00
]

for a, b in donald_blocked:
    s.add(Or(S + 30 <= a, S >= b))

if s.check() == sat:
    m = s.model()
    start = m[S].as_long()
    end = start + 30
    start_time = to_time(start)
    end_time = to_time(end)
    print(f"Monday {start_time}:{end_time}")
else:
    print("No solution found")