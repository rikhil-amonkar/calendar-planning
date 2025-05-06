from z3 import *

s = Optimize()
day = Int('day')
start = Int('start')

# Day must be 0 (Monday) to 3 (Thursday)
s.add(day >= 0, day <= 3)
s.add(start >= 0, start + 30 <= 480)  # 30 minutes meeting

# Monday constraints (day 0)
s.add(Implies(day == 0,
    And(
        # Alexis's Monday busy: 0-60 (9:00-10:00), 90-180 (10:30-12:00), 210-450 (12:30-16:30)
        Or(start + 30 <= 0, start >= 60),
        Or(start + 30 <= 90, start >= 180),
        Or(start + 30 <= 210, start >= 450)
    )
))

# Tuesday constraints (day 1)
s.add(Implies(day == 1,
    And(
        # Mary's Tuesday busy: 60-90 (10:00-10:30), 390-420 (15:30-16:00)
        Or(start + 30 <= 60, start >= 90),
        Or(start + 30 <= 390, start >= 420),
        # Alexis's Tuesday busy: 0-60 (9:00-10:00), 90-150 (10:30-11:30), 180-390 (12:00-15:30), 420-480 (16:00-17:00)
        Or(start + 30 <= 0, start >= 60),
        Or(start + 30 <= 90, start >= 150),
        Or(start + 30 <= 180, start >= 390),
        Or(start + 30 <= 420, start >= 480)
    )
))

# Wednesday constraints (day 2)
s.add(Implies(day == 2,
    And(
        # Mary's Wednesday busy: 30-60 (9:30-10:00), 360-390 (15:00-15:30)
        Or(start + 30 <= 30, start >= 60),
        Or(start + 30 <= 360, start >= 390),
        # Alexis's Wednesday busy: 0-120 (9:00-11:00), 150-480 (11:30-17:00)
        Or(start + 30 <= 0, start >= 120),
        Or(start + 30 <= 150, start >= 480)
    )
))

# Thursday constraints (day 3)
s.add(Implies(day == 3,
    And(
        # Mary's Thursday busy: 0-60 (9:00-10:00), 90-150 (10:30-11:30)
        Or(start + 30 <= 0, start >= 60),
        Or(start + 30 <= 90, start >= 150),
        # Alexis's Thursday busy: 60-180 (10:00-12:00), 300-330 (14:00-14:30), 390-420 (15:30-16:00), 450-480 (16:30-17:00)
        Or(start + 30 <= 60, start >= 180),
        Or(start + 30 <= 300, start >= 330),
        Or(start + 30 <= 390, start >= 420),
        Or(start + 30 <= 450, start >= 480)
    )
))

# Optimize for earliest possible time
s.minimize(day * 1000 + start)

if s.check() == sat:
    m = s.model()
    d = m[day].as_long()
    st = m[start].as_long()
    days = ["Monday", "Tuesday", "Wednesday", "Thursday"]
    hours = 9 + st // 60
    minutes = st % 60
    print(f"Meeting can be scheduled on {days[d]} at {hours:02d}:{minutes:02d}")
else:
    print("No valid time found.")