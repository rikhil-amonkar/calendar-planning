from z3 import *

s = Optimize()
day = Int('day')
start = Int('start')

# Day must be 0 (Monday) or 1 (Tuesday)
s.add(Or(day == 0, day == 1))

# Meeting duration constraints based on day
s.add(Or(
    And(day == 0, start >= 0, start + 30 <= 480),  # Monday 9:00-17:00
    And(day == 1, start >= 0, start + 30 <= 450)   # Tuesday 9:00-16:30
))

# Jesse's schedule constraints
# Monday: 13:30-14:00 (270-300), 14:30-15:00 (330-360)
s.add(Implies(day == 0, Or(start + 30 <= 270, start >= 300)))
s.add(Implies(day == 0, Or(start + 30 <= 330, start >= 360)))

# Tuesday: 9:00-9:30 (0-30), 13:00-13:30 (240-270), 14:00-15:00 (300-360)
s.add(Implies(day == 1, Or(start + 30 <= 0, start >= 30)))
s.add(Implies(day == 1, Or(start + 30 <= 240, start >= 270)))
s.add(Implies(day == 1, Or(start + 30 <= 300, start >= 360)))

# Lawrence's schedule constraints
# Monday: Entire day busy (0-480)
s.add(Implies(day == 0, Or(start + 30 <= 0, start >= 480)))

# Tuesday: 9:30-10:30 (30-90), 11:30-12:30 (150-180), 13:00-13:30 (240-270), 14:30-15:00 (330-360), 15:30-16:30 (390-450)
s.add(Implies(day == 1, Or(start + 30 <= 30, start >= 90)))
s.add(Implies(day == 1, Or(start + 30 <= 150, start >= 180)))
s.add(Implies(day == 1, Or(start + 30 <= 240, start >= 270)))
s.add(Implies(day == 1, Or(start + 30 <= 330, start >= 360)))
s.add(Implies(day == 1, Or(start + 30 <= 390, start >= 450)))

# Minimize day and start time to find earliest slot
s.minimize(day * 1000 + start)

if s.check() == sat:
    model = s.model()
    d = model[day].as_long()
    st = model[start].as_long()
    day_str = "Monday" if d == 0 else "Tuesday"
    hours = 9 + st // 60
    minutes = st % 60
    print(f"Meeting can be scheduled on {day_str} at {hours:02d}:{minutes:02d}")
else:
    print("No valid time found.")