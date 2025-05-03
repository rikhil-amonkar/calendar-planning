from z3 import Optimize, Real, Or

s = Optimize()
start = Real('start')

# Meeting duration is 0.5 hours (30 minutes)
duration = 0.5

# Global constraint: meeting must be within 9:00 to 17:00
s.add(start >= 9.0)
s.add(start + duration <= 17.0)

# Jesse's busy times (10:00-10:30, 15:30-16:00)
jesse_busy = [(10.0, 10.5), (15.5, 16.0)]
for begin, end in jesse_busy:
    s.add(Or(start + duration <= begin, start >= end))

# Megan's busy times (10:30-11:00, 11:30-12:30, 13:30-14:30, 15:00-16:30)
megan_busy = [(10.5, 11.0), (11.5, 12.5), (13.5, 14.5), (15.0, 16.5)]
for begin, end in megan_busy:
    s.add(Or(start + duration <= begin, start >= end))

# Kathryn has no meetings (no constraints)

# Optimize for earliest start time
s.minimize(start)

if s.check() == sat:
    m = s.model()
    start_time = m[start].as_fraction()
    hours = int(start_time.numerator // start_time.denominator)
    minutes = int((start_time.numerator % start_time.denominator) * 60 / start_time.denominator)
    print(f"Meeting can be scheduled at {hours:02d}:{minutes:02d}")
else:
    print("No suitable time found.")