from z3 import Solver, Real, Or

s = Solver()
start = Real('start')

# Meeting duration is 0.5 hours (30 minutes)
duration = 0.5

# Global constraint: meeting must be within 9:00 to 17:00
s.add(start >= 9.0)
s.add(start + duration <= 17.0)

# Scott's busy times (9:30-10:30, 13:30-14:00, 14:30-15:00, 15:30-16:00, 16:30-17:00)
scott_busy = [(9.5, 10.5), (13.5, 14.0), (14.5, 15.0), (15.5, 16.0), (16.5, 17.0)]
for begin, end in scott_busy:
    s.add(Or(start + duration <= begin, start >= end))

# Gabriel has no meetings (no constraints)

# Christine's busy times (9:00-10:00, 10:30-12:30, 13:00-17:00)
christine_busy = [(9.0, 10.0), (10.5, 12.5), (13.0, 17.0)]
for begin, end in christine_busy:
    s.add(Or(start + duration <= begin, start >= end))

if s.check() == sat:
    m = s.model()
    start_time = m[start].as_fraction()
    hours = int(start_time.numerator // start_time.denominator)
    minutes = int((start_time.numerator % start_time.denominator) * 60 / start_time.denominator)
    print(f"Meeting can be scheduled at {hours:02d}:{minutes:02d}")
else:
    print("No suitable time found.")