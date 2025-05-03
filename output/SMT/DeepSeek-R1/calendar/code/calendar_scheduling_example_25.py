from z3 import Solver, Real, Or

s = Solver()
start = Real('start')

# Meeting duration is 1 hour
duration = 1.0

# Global constraint: meeting must be within 9:00 to 17:00
s.add(start >= 9.0)
s.add(start + duration <= 17.0)

# Apply Pamela's preference: meeting must end by 14:30
s.add(start + duration <= 14.5)  # 14:30 = 14.5 hours

# Anthony's busy times (9:30-10:00, 12:00-13:00, 16:00-16:30)
anthony_busy = [(9.5, 10.0), (12.0, 13.0), (16.0, 16.5)]
for begin, end in anthony_busy:
    s.add(Or(start + duration <= begin, start >= end))

# Pamela's busy times (9:30-10:00, 16:30-17:00)
pamela_busy = [(9.5, 10.0), (16.5, 17.0)]
for begin, end in pamela_busy:
    s.add(Or(start + duration <= begin, start >= end))

# Zachary's busy times (9:00-11:30, 12:00-12:30, 13:00-13:30, 14:30-15:00, 16:00-17:00)
zachary_busy = [(9.0, 11.5), (12.0, 12.5), (13.0, 13.5), (14.5, 15.0), (16.0, 17.0)]
for begin, end in zachary_busy:
    s.add(Or(start + duration <= begin, start >= end))

if s.check() == sat:
    m = s.model()
    start_time = m[start].as_fraction()
    hours = int(start_time.numerator // start_time.denominator)
    minutes = int((start_time.numerator % start_time.denominator) * 60 / start_time.denominator)
    print(f"Meeting can be scheduled at {hours:02d}:{minutes:02d}")
else:
    print("No suitable time found.")