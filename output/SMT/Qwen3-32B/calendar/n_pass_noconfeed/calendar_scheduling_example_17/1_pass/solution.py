from z3 import *

def minutes_to_time(m):
    h = m // 60
    mi = m % 60
    return f"{h:02d}:{mi:02d}"

solver = Solver()
start_time = Int('start_time')

# Work hours from 9:00 (540) to 17:00 (1020)
solver.add(start_time >= 540)
solver.add(start_time <= 990)  # start_time + 30 <= 1020

# Helen's constraint: meeting must start by 13:00 (780)
solver.add(start_time <= 780)

# Margaret's blocked intervals
blocked_marg = [
    (540, 600),  # 9:00-10:00
    (630, 660),  # 10:30-11:00
    (690, 720),  # 11:30-12:00
    (780, 810),  # 13:00-13:30
    (900, 930),  # 15:00-15:30
]
for b_start, b_end in blocked_marg:
    solver.add(Or(start_time + 30 <= b_start, start_time >= b_end))

# Donna's blocked intervals
blocked_donna = [
    (870, 900),  # 14:30-15:00
    (960, 990),  # 16:00-16:30
]
for b_start, b_end in blocked_donna:
    solver.add(Or(start_time + 30 <= b_start, start_time >= b_end))

# Helen's blocked intervals
blocked_helen = [
    (540, 570),  # 9:00-9:30
    (600, 690),  # 10:00-11:30
    (780, 840),  # 13:00-14:00
    (870, 900),  # 14:30-15:00
    (930, 1020),  # 15:30-17:00
]
for b_start, b_end in blocked_helen:
    solver.add(Or(start_time + 30 <= b_start, start_time >= b_end))

if solver.check() == sat:
    model = solver.model()
    st = model[start_time].as_long()
    start = st
    end = st + 30
    day = "Monday"
    start_str = minutes_to_time(start)
    end_str = minutes_to_time(end)
    print(f"{start_str}:{end_str} {day}")
else:
    print("No solution found")