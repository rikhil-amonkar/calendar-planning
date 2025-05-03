from z3 import Solver, Real, Or

s = Solver()
start = Real('start')

# Meeting duration is 1 hour
duration = 1.0

# Global constraint: meeting must be within 9:00 to 17:00
s.add(start >= 9.0)
s.add(start + duration <= 17.0)

# David has no meetings (no constraints)

# Debra's busy times (9:30-10:00, 11:00-11:30, 12:00-13:00, 14:00-14:30, 16:00-16:30)
debra_busy = [(9.5, 10.0), (11.0, 11.5), (12.0, 13.0), (14.0, 14.5), (16.0, 16.5)]
for begin, end in debra_busy:
    s.add(Or(start + duration <= begin, start >= end))

# Kevin's busy times (9:00-12:00, 14:00-17:00)
kevin_busy = [(9.0, 12.0), (14.0, 17.0)]
for begin, end in kevin_busy:
    s.add(Or(start + duration <= begin, start >= end))

if s.check() == sat:
    m = s.model()
    start_time = m[start].as_fraction()
    hours = int(start_time.numerator // start_time.denominator)
    minutes = int((start_time.numerator % start_time.denominator) * 60 / start_time.denominator)
    print(f"Meeting can be scheduled at {hours:02d}:{minutes:02d}")
else:
    print("No suitable time found.")