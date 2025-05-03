from z3 import Solver, Real, Or

s = Solver()
start = Real('start')

# Meeting duration is 0.5 hours (30 minutes)
duration = 0.5

# Global constraint: meeting must be within 9:00 to 17:00
s.add(start >= 9.0)
s.add(start + duration <= 17.0)

# Apply Christine's preference: start after 12:00
s.add(start >= 12.0)

# Joyce's busy times (11:00-11:30, 13:30-14:00, 14:30-16:30)
joyce_busy = [(11.0, 11.5), (13.5, 14.0), (14.5, 16.5)]
for begin, end in joyce_busy:
    s.add(Or(start + duration <= begin, start >= end))

# Christine has no meetings (only preference constraint applied)

# Alexander's busy times (9:00-11:00, 12:00-12:30, 13:30-15:00, 15:30-16:00, 16:30-17:00)
alexander_busy = [(9.0, 11.0), (12.0, 12.5), (13.5, 15.0), (15.5, 16.0), (16.5, 17.0)]
for begin, end in alexander_busy:
    s.add(Or(start + duration <= begin, start >= end))

if s.check() == sat:
    m = s.model()
    start_time = m[start].as_fraction()
    hours = int(start_time.numerator // start_time.denominator)
    minutes = int((start_time.numerator % start_time.denominator) * 60 / start_time.denominator)
    print(f"Meeting can be scheduled at {hours:02d}:{minutes:02d}")
else:
    print("No suitable time found.")