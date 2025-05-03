from z3 import Solver, Real, Or

s = Solver()
start = Real('start')

# Meeting duration is 1 hour
duration = 1.0

# Global constraint: meeting must be within 9:00 to 17:00
s.add(start >= 9.0)
s.add(start + duration <= 17.0)

# Kevin's busy times (9:00-10:00, 10:30-11:30, 12:00-15:30, 16:30-17:00)
kevin_busy = [(9.0, 10.0), (10.5, 11.5), (12.0, 15.5), (16.5, 17.0)]
for begin, end in kevin_busy:
    s.add(Or(start + duration <= begin, start >= end))

# Katherine and Nicole have no meetings (no additional constraints)

if s.check() == sat:
    m = s.model()
    start_time = m[start].as_fraction()
    hours = int(start_time.numerator // start_time.denominator)
    minutes = int((start_time.numerator % start_time.denominator) * 60 / start_time.denominator)
    print(f"Meeting can be scheduled at {hours:02d}:{minutes:02d}")
else:
    print("No suitable time found.")