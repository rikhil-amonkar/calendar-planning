from z3 import *

s = Optimize()
day = Int('day')
start = Int('start')

s.add(day >= 0, day <= 1)  # 0:Monday, 1:Tuesday
s.add(start >= 0, start + 60 <= 480)  # 1-hour meeting within 9:00-17:00

# Monday constraints
s.add(Implies(day == 0,
    And(
        # Russell's busy: 90-120 (10:30-11:00)
        Or(start + 60 <= 90, start >= 120),
        # Alexander's busy: 0-150 (9:00-11:30), 180-330 (12:00-14:30), 360-480 (15:00-17:00)
        Or(start + 60 <= 0, And(start >= 150, start + 60 <= 180)),  # Only possible 11:30-12:00 (30min)
        Or(start + 60 <= 180, start >= 330),
        Or(start + 60 <= 360, start >= 480)
    )
))

# Tuesday constraints
s.add(Implies(day == 1,
    And(
        # Russell's busy: 240-270 (13:00-13:30)
        Or(start + 60 <= 240, start >= 270),
        # Alexander's busy: 0-60 (9:00-10:00), 240-300 (13:00-14:00), 360-390 (15:00-15:30), 420-450 (16:00-16:30)
        Or(
            And(start >= 60, start + 60 <= 240),   # 10:00-13:00
            And(start >= 300, start + 60 <= 360)   # 14:00-15:00
        )
    )
))

# Preference penalty for Tuesday before 13:30 (270 minutes)
penalty = If(And(day == 1, start < 270), 1000, 0)
s.minimize(penalty + day * 1000 + start)

if s.check() == sat:
    m = s.model()
    d = m[day].as_long()
    st = m[start].as_long()
    days = ["Monday", "Tuesday"]
    hours = 9 + st // 60
    minutes = st % 60
    print(f"Meeting can be scheduled on {days[d]} at {hours:02d}:{minutes:02d}")
else:
    print("No valid time found.")