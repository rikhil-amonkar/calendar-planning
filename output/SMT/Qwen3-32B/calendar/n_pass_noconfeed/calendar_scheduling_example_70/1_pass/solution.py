from z3 import *

def to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

start = Int('start')
s = Optimize()

# Work hours constraints (9:00-17:00 is 540 to 1020 minutes)
s.add(start >= 540)
s.add(start + 30 <= 1020)

# Denise's busy periods
denise_busy = [(720, 750), (930, 960)]
for b_start, b_end in denise_busy:
    s.add(Or(start + 30 <= b_start, start >= b_end))

# Natalie's busy periods
natalie_busy = [(540, 690), (720, 780), (840, 870), (900, 1020)]
for b_start, b_end in natalie_busy:
    s.add(Or(start + 30 <= b_start, start >= b_end))

# Angela has no constraints

s.minimize(start)

if s.check() == sat:
    m = s.model()
    start_time = m[start].as_long()
    start_str = to_time(start_time)
    end_str = to_time(start_time + 30)
    print(f"{start_str}:{end_str} Monday")
else:
    print("No solution")