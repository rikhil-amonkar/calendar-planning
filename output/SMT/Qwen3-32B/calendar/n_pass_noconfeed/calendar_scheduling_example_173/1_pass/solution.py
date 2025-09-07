from z3 import *

def time_format(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

s = Solver()

start_time = Int('start_time')

# Meeting must be between 9:00 (540) and 17:00 (1020)
# Harold cannot meet after 13:00 (780) => end_time <= 780 => start_time <= 750
s.add(start_time >= 540)
s.add(start_time <= 750)

# Busy intervals for each participant in minutes since midnight
jacqueline = [(540, 570), (660, 690), (750, 780), (930, 960)]
harold = [(600, 630), (780, 810), (900, 1020)]
arthur = [(540, 570), (600, 750), (870, 900), (930, 1020)]
kelly = [(540, 570), (600, 660), (690, 750), (840, 900), (930, 960)]

def add_constraints(intervals):
    for (s_i, e_i) in intervals:
        s.add(Or(start_time + 30 <= s_i, e_i <= start_time))

add_constraints(jacqueline)
add_constraints(harold)
add_constraints(arthur)
add_constraints(kelly)

if s.check() == sat:
    m = s.model()
    st = m[start_time].as_long()
    et = st + 30
    day = "Monday"
    print(f"{day}: {time_format(st)}:{time_format(et)}")
else:
    print("No solution found.")