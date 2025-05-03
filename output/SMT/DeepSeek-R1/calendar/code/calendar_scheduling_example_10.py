from z3 import Solver, Real, Or

s = Solver()
start = Real('start')

# Meeting duration is 0.5 hours (30 minutes)
duration = 0.5

# Global constraint: meeting must be within 9:00 to 17:00
s.add(start >= 9.0)
s.add(start + duration <= 17.0)

# Apply Janet's preference: meeting must end by 12:00
s.add(start + duration <= 12.0)

# Diana's busy times (11:30-12:00, 13:00-13:30)
diana_busy = [(11.5, 12.0), (13.0, 13.5)]
for begin, end in diana_busy:
    s.add(Or(start + duration <= begin, start >= end))

# Ethan has no meetings (no constraints)

# Janet's busy times (9:00-10:00, 12:30-13:00, 14:00-15:00, 15:30-17:00)
janet_busy = [(9.0, 10.0), (12.5, 13.0), (14.0, 15.0), (15.5, 17.0)]
for begin, end in janet_busy:
    s.add(Or(start + duration <= begin, start >= end))

if s.check() == sat:
    m = s.model()
    start_time = m[start].as_fraction()
    hours = int(start_time.numerator // start_time.denominator)
    minutes = int((start_time.numerator % start_time.denominator) * 60 / start_time.denominator)
    print(f"Meeting can be scheduled at {hours:02d}:{minutes:02d}")
else:
    print("No suitable time found.")