from z3 import *

def to_time(mins):
    h = mins // 60
    m = mins % 60
    return f"{h:02d}:{m:02d}"

solver = Solver()
start_time = Int('start_time')

# Work hours from 9:00 (540) to 17:00 (1020), meeting duration 30 mins
solver.add(And(start_time >= 540, start_time <= 990))

# Cynthia's busy intervals (minutes since 00:00)
cynthia = [(540, 570), (600, 630), (810, 870), (900, 960)]
for b_start, b_end in cynthia:
    solver.add(Or(start_time + 30 <= b_start, start_time >= b_end))

# Ann's busy intervals
ann = [(600, 660), (780, 810), (840, 900), (960, 990)]
for b_start, b_end in ann:
    solver.add(Or(start_time + 30 <= b_start, start_time >= b_end))

# Catherine's busy intervals
catherine = [(540, 690), (750, 810), (870, 1020)]
for b_start, b_end in catherine:
    solver.add(Or(start_time + 30 <= b_start, start_time >= b_end))

# Kyle's busy intervals
kyle = [(540, 570), (600, 690), (720, 750), (780, 870), (900, 960)]
for b_start, b_end in kyle:
    solver.add(Or(start_time + 30 <= b_start, start_time >= b_end))

if solver.check() == sat:
    model = solver.model()
    start = model[start_time].as_long()
    end = start + 30
    start_str = to_time(start)
    end_str = to_time(end)
    print(f"Monday {start_str}:{end_str}")
else:
    print("No solution found")