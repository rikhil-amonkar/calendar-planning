from z3 import Solver, Real, Or

s = Solver()
start = Real('start')

# Meeting duration is 0.5 hours (30 minutes)
duration = 0.5

# Global constraint: meeting must be within 9:00 to 17:00
s.add(start >= 9.0)
s.add(start + duration <= 17.0)

# Apply Helen's preference: meeting must end by 13:30
s.add(start + duration <= 13.5)  # 13:30 = 13.5 hours

# Margaret's busy times (9:00-10:00, 10:30-11:00, 11:30-12:00, 13:00-13:30, 15:00-15:30)
margaret_busy = [(9.0, 10.0), (10.5, 11.0), (11.5, 12.0), (13.0, 13.5), (15.0, 15.5)]
for begin, end in margaret_busy:
    s.add(Or(start + duration <= begin, start >= end))

# Donna's busy times (14:30-15:00, 16:00-16:30)
donna_busy = [(14.5, 15.0), (16.0, 16.5)]
for begin, end in donna_busy:
    s.add(Or(start + duration <= begin, start >= end))

# Helen's busy times (9:00-9:30, 10:00-11:30, 13:00-14:00, 14:30-15:00, 15:30-17:00)
helen_busy = [(9.0, 9.5), (10.0, 11.5), (13.0, 14.0), (14.5, 15.0), (15.5, 17.0)]
for begin, end in helen_busy:
    s.add(Or(start + duration <= begin, start >= end))

if s.check() == sat:
    m = s.model()
    start_time = m[start].as_fraction()
    hours = int(start_time.numerator // start_time.denominator)
    minutes = int((start_time.numerator % start_time.denominator) * 60 / start_time.denominator)
    print(f"Meeting can be scheduled at {hours:02d}:{minutes:02d}")
else:
    print("No suitable time found.")