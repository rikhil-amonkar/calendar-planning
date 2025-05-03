from z3 import Solver, Real, Or

s = Solver()
start = Real('start')

# Meeting duration is 0.5 hours (30 minutes)
duration = 0.5

# Global constraint: meeting must be within 9:00 to 17:00
s.add(start >= 9.0)
s.add(start + duration <= 17.0)

# Apply Brandon's preference: start after 14:30
s.add(start >= 14.5)

# Brandon's busy times (13:00-14:00, 15:30-16:00, 16:30-17:00)
brandon_busy = [(13.0, 14.0), (15.5, 16.0), (16.5, 17.0)]
for begin, end in brandon_busy:
    s.add(Or(start + duration <= begin, start >= end))

# Jerry has no meetings (no constraints)

# Bradley's busy times (9:00-11:30, 12:00-15:00, 16:00-16:30)
bradley_busy = [(9.0, 11.5), (12.0, 15.0), (16.0, 16.5)]
for begin, end in bradley_busy:
    s.add(Or(start + duration <= begin, start >= end))

if s.check() == sat:
    m = s.model()
    start_time = m[start].as_fraction()
    hours = int(start_time.numerator // start_time.denominator)
    minutes = int((start_time.numerator % start_time.denominator) * 60 / start_time.denominator)
    print(f"Meeting can be scheduled at {hours:02d}:{minutes:02d}")
else:
    print("No suitable time found.")