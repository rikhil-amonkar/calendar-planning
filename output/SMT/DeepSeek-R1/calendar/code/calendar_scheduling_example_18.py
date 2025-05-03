from z3 import Solver, Real, Or

s = Solver()
start = Real('start')

# Meeting duration is 0.5 hours (30 minutes)
duration = 0.5

# Global constraint: meeting must be within 9:00 to 17:00
s.add(start >= 9.0)
s.add(start + duration <= 17.0)

# Apply Billy's preference: meeting must end by 15:30
s.add(start + duration <= 15.5)

# Brian has no meetings (no constraints)

# Billy's busy times (10:00-10:30, 11:30-12:00, 14:00-14:30, 16:30-17:00)
billy_busy = [(10.0, 10.5), (11.5, 12.0), (14.0, 14.5), (16.5, 17.0)]
for begin, end in billy_busy:
    s.add(Or(start + duration <= begin, start >= end))

# Patricia's busy times (9:00-12:30, 13:30-14:00, 14:30-16:00, 16:30-17:00)
patricia_busy = [(9.0, 12.5), (13.5, 14.0), (14.5, 16.0), (16.5, 17.0)]
for begin, end in patricia_busy:
    s.add(Or(start + duration <= begin, start >= end))

if s.check() == sat:
    m = s.model()
    start_time = m[start].as_fraction()
    hours = int(start_time.numerator // start_time.denominator)
    minutes = int((start_time.numerator % start_time.denominator) * 60 / start_time.denominator)
    print(f"Meeting can be scheduled at {hours:02d}:{minutes:02d}")
else:
    print("No suitable time found.")