from z3 import Solver, Real, Or

s = Solver()
start = Real('start')

# Meeting duration is 0.5 hours (30 minutes)
duration = 0.5

# Global constraint: meeting must be within 9:00 to 17:00
s.add(start >= 9.0)
s.add(start + duration <= 17.0)

# Diane's busy times (9:00-9:30, 12:00-12:30, 14:30-15:30)
diane_busy = [(9.0, 9.5), (12.0, 12.5), (14.5, 15.5)]
for begin, end in diane_busy:
    s.add(Or(start + duration <= begin, start >= end))

# Kelly's busy times (9:30-10:00, 10:30-11:00)
kelly_busy = [(9.5, 10.0), (10.5, 11.0)]
for begin, end in kelly_busy:
    s.add(Or(start + duration <= begin, start >= end))

# Deborah's busy times (9:00-9:30, 10:00-14:00, 14:30-17:00)
deborah_busy = [(9.0, 9.5), (10.0, 14.0), (14.5, 17.0)]
for begin, end in deborah_busy:
    s.add(Or(start + duration <= begin, start >= end))

if s.check() == sat:
    m = s.model()
    start_time = m[start].as_fraction()
    hours = int(start_time.numerator // start_time.denominator)
    minutes = int((start_time.numerator % start_time.denominator) * 60 / start_time.denominator)
    print(f"Meeting can be scheduled at {hours:02d}:{minutes:02d}")
else:
    print("No suitable time found.")