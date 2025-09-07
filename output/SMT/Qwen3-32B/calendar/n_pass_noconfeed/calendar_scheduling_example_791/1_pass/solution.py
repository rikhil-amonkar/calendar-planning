from z3 import *

day = Int('day')
start = Int('start')

s = Solver()

# Day must be 0 (Monday), 1 (Tuesday), or 2 (Wednesday)
s.add(Or(day == 0, day == 1, day == 2))

# Constraints on start time based on the day
s.add(Implies(day == 0, And(start >= 540, start <= 990)))
s.add(Implies(day == 1, And(start >= 540, start <= 990)))
s.add(Implies(day == 2, And(start >= 540, start <= 780)))

# Nicole's Monday constraints
nicole_mon = And(
    Or(start + 30 <= 540, start >= 570),
    Or(start + 30 <= 780, start >= 810),
    Or(start + 30 <= 870, start >= 930)
)
# Ruth's Monday constraints
ruth_mon = Or(start + 30 <= 540, start >= 1020)
s.add(Implies(day == 0, And(nicole_mon, ruth_mon)))

# Nicole's Tuesday constraints
nicole_tue = And(
    Or(start + 30 <= 540, start >= 570),
    Or(start + 30 <= 690, start >= 810),
    Or(start + 30 <= 870, start >= 930)
)
# Ruth's Tuesday constraints
ruth_tue = Or(start + 30 <= 540, start >= 1020)
s.add(Implies(day == 1, And(nicole_tue, ruth_tue)))

# Nicole's Wednesday constraints
nicole_wed = And(
    Or(start + 30 <= 600, start >= 660),
    start <= 720
)
# Ruth's Wednesday constraints
ruth_wed = And(
    Or(start + 30 <= 540, start >= 630),
    Or(start + 30 <= 660, start >= 690),
    Or(start + 30 <= 720, start >= 750)
)
s.add(Implies(day == 2, And(nicole_wed, ruth_wed)))

if s.check() == sat:
    m = s.model()
    day_val = m[day].as_long()
    start_val = m[start].as_long()
    days = ['Monday', 'Tuesday', 'Wednesday']
    day_name = days[day_val]
    start_h = start_val // 60
    start_m = start_val % 60
    end_val = start_val + 30
    end_h = end_val // 60
    end_m = end_val % 60
    time_range = f"{start_h:02d}:{start_m:02d}:{end_h:02d}:{end_m:02d}"
    print(f"{time_range} {day_name}")
else:
    print("No solution")