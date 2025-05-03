from z3 import Optimize, Real, Or

s = Optimize()
start = Real('start')

# Meeting duration is 0.5 hours (30 minutes)
duration = 0.5

# Global constraint: meeting must be within 9:00 to 17:00
s.add(start >= 9.0)
s.add(start + duration <= 17.0)

# Brittany's busy times (13:00-13:30, 16:00-16:30)
brittany_busy = [(13.0, 13.5), (16.0, 16.5)]
for begin, end in brittany_busy:
    s.add(Or(start + duration <= begin, start >= end))

# Doris's busy times (9:00-11:00, 11:30-14:30, 15:00-17:00)
doris_busy = [(9.0, 11.0), (11.5, 14.5), (15.0, 17.0)]
for begin, end in doris_busy:
    s.add(Or(start + duration <= begin, start >= end))

# Emily has no meetings (no constraints)

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