from z3 import Solver, Real, Or

s = Solver()
start = Real('start')

# Meeting duration is 1 hour
duration = 1.0

# Global constraint: meeting must be within 9:00 to 17:00
s.add(start >= 9.0)
s.add(start + duration <= 17.0)

# Scott's busy times (11:30-12:00, 15:30-16:00)
scott_busy = [(11.5, 12.0), (15.5, 16.0)]
for begin, end in scott_busy:
    s.add(Or(start + duration <= begin, start >= end))

# Kimberly's busy times (11:00-12:00, 12:30-13:00, 13:30-14:00, 14:30-15:00, 15:30-17:00)
kimberly_busy = [(11.0, 12.0), (12.5, 13.0), (13.5, 14.0), (14.5, 15.0), (15.5, 17.0)]
for begin, end in kimberly_busy:
    s.add(Or(start + duration <= begin, start >= end))

# Bobby has no meetings (no constraints)

if s.check() == sat:
    m = s.model()
    start_time = m[start].as_fraction()
    hours = int(start_time.numerator // start_time.denominator)
    minutes = int((start_time.numerator % start_time.denominator) * 60 / start_time.denominator)
    print(f"Meeting can be scheduled at {hours:02d}:{minutes:02d}")
else:
    print("No suitable time found.")