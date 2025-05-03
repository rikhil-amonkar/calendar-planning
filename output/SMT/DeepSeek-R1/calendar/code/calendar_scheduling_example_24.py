from z3 import Solver, Real, Or

s = Solver()
start = Real('start')

# Meeting duration is 0.5 hours (30 minutes)
duration = 0.5

# Global constraint: meeting must be within 9:00 to 17:00
s.add(start >= 9.0)
s.add(start + duration <= 17.0)

# Apply Benjamin's preference: meeting must end by 9:30
s.add(start + duration <= 9.5)  # 9:30 = 9.5 hours

# Brenda's busy times (9:30-10:00, 11:30-12:30, 14:00-16:30)
brenda_busy = [(9.5, 10.0), (11.5, 12.5), (14.0, 16.5)]
for begin, end in brenda_busy:
    s.add(Or(start + duration <= begin, start >= end))

# Hannah and Benjamin have no meetings (no additional constraints)

if s.check() == sat:
    m = s.model()
    start_time = m[start].as_fraction()
    hours = int(start_time.numerator // start_time.denominator)
    minutes = int((start_time.numerator % start_time.denominator) * 60 / start_time.denominator)
    print(f"Meeting can be scheduled at {hours:02d}:{minutes:02d}")
else:
    print("No suitable time found.")