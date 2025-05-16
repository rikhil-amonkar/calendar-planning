from z3 import *

s = Solver()

day = Int('day')
start = Int('start')
duration = 30  # minutes

s.add(day >= 0, day <= 2)  # 0: Monday, 1: Tuesday, 2: Wednesday
s.add(start >= 0)
s.add(start + duration <= 480)  # End by 17:00 (480 minutes from 9:00)

# Susan prefers not to meet on Tuesday (treated as hard constraint)
s.add(day != 1)

# Monday constraints
# Sandra cannot meet after 16:00 (420 minutes)
s.add(Implies(day == 0, start + duration <= 420))
# Susan's blocked periods on Monday: 12:30-13:00 (210-240) and 13:30-14:00 (270-300)
s.add(Implies(day == 0, Or(start + duration <= 210, start >= 240)))
s.add(Implies(day == 0, Or(start + duration <= 270, start >= 300)))
# Sandra's available periods on Monday: 13:00-14:00 (240-300) and 15:00-16:00 (360-420)
s.add(Implies(day == 0, Or(
    And(start >= 240, start + duration <= 300),
    And(start >= 360, start + duration <= 420)
)))

# Wednesday constraints
# Susan's blocked periods: 9:30-10:30 (30-90), 14:00-14:30 (300-330), 15:30-16:30 (390-420)
s.add(Implies(day == 2, Or(start + duration <= 30, start >= 90)))
s.add(Implies(day == 2, Or(start + duration <= 300, start >= 330)))
s.add(Implies(day == 2, Or(start + duration <= 390, start >= 420)))
# Sandra's available periods on Wednesday: 11:30-12:00 (150-180) and 12:30-13:00 (210-240)
s.add(Implies(day == 2, Or(
    And(start >= 150, start + duration <= 180),
    And(start >= 210, start + duration <= 240)
)))

if s.check() == sat:
    m = s.model()
    d = m[day].as_long()
    st = m[start].as_long()
    days = ['Monday', 'Tuesday', 'Wednesday']
    start_h = 9 + st // 60
    start_m = st % 60
    end_h = 9 + (st + duration) // 60
    end_m = (st + duration) % 60
    print(f"{days[d]} {start_h:02d}:{start_m:02d}-{end_h:02d}:{end_m:02d}")
else:
    print("No valid slot found")