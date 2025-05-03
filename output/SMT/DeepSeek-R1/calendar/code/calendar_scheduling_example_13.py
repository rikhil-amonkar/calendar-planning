from z3 import Solver, Real, Or

s = Solver()
start = Real('start')

# Meeting duration is 0.5 hours (30 minutes)
duration = 0.5

# Global constraint: meeting must be within 9:00 to 17:00
s.add(start >= 9.0)
s.add(start + duration <= 17.0)

# Apply Gerald's preference: start after 13:00
s.add(start >= 13.0)

# Gerald's busy times (9:00-9:30, 13:00-14:00, 15:00-15:30, 16:00-17:00)
gerald_busy = [(9.0, 9.5), (13.0, 14.0), (15.0, 15.5), (16.0, 17.0)]
for begin, end in gerald_busy:
    s.add(Or(start + duration <= begin, start >= end))

# Roy has no meetings (no constraints)

# Barbara's busy times (9:30-10:00, 11:30-14:00, 14:30-15:00, 15:30-17:00)
barbara_busy = [(9.5, 10.0), (11.5, 14.0), (14.5, 15.0), (15.5, 17.0)]
for begin, end in barbara_busy:
    s.add(Or(start + duration <= begin, start >= end))

if s.check() == sat:
    m = s.model()
    start_time = m[start].as_fraction()
    hours = int(start_time.numerator // start_time.denominator)
    minutes = int((start_time.numerator % start_time.denominator) * 60 / start_time.denominator)
    print(f"Meeting can be scheduled at {hours:02d}:{minutes:02d}")
else:
    print("No suitable time found.")