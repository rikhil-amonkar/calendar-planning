from z3 import *

def to_time(mins):
    h = mins // 60
    m = mins % 60
    return f"{h:02d}:{m:02d}"

solver = Solver()

day = Int('day')
start = Int('start')
end = start + 60

solver.add(And(day >= 0, day <= 3))
solver.add(And(start >= 540, start <= 960))  # since end is start + 60 <= 1020 (17:00)

# Busy intervals for each day (0=Monday, 1=Tuesday, 2=Wednesday, 3=Thursday)
busy_intervals = [
    # Monday: Natalie and William's intervals
    [(540, 570), (600, 720), (750, 780), (840, 870), (900, 990), (570, 660), (690, 1020)],
    # Tuesday
    [(540, 570), (600, 630), (750, 840), (960, 1020), (540, 780), (810, 960)],
    # Wednesday
    [(660, 690), (960, 990), (540, 750), (780, 870), (930, 960), (990, 1020)],
    # Thursday
    [(600, 660), (690, 900), (930, 960), (990, 1020), (540, 630), (660, 690), (720, 750), (780, 840), (900, 1020)]
]

for d in range(4):
    for (bs, be) in busy_intervals[d]:
        c = Or(day != d, Or(start >= be, bs >= end))
        solver.add(c)

if solver.check() == sat:
    m = solver.model()
    d_val = m[day].as_long()
    s_val = m[start].as_long()
    e_val = s_val + 60
    days = ['Monday', 'Tuesday', 'Wednesday', 'Thursday']
    day_name = days[d_val]
    print(f"SOLUTION:")
    print(f"Day: {day_name}")
    print(f"Start Time: {to_time(s_val)}")
    print(f"End Time: {to_time(e_val)}")
else:
    print("No solution found.")