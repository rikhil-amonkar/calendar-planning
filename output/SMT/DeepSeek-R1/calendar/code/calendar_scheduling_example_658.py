from z3 import *

s = Optimize()

day = Int('day')
start_time = Int('start_time')

# Day must be Tuesday (1) since Albert is busy all Monday
s.add(day == 1)

# Time constraints (9:00-17:00 converted to minutes since 9:00)
s.add(start_time >= 0)
s.add(start_time + 30 <= 480)  # 8 hours = 480 minutes

# Shirley's Tuesday constraints
s.add(Or(start_time + 30 <= 90))  # Can't end after 10:30 (90 minutes)
s.add(Or(start_time + 30 <= 30, start_time >= 60))  # Avoid 9:30-10:00 block (30-60 mins)

# Albert's Tuesday schedule constraints
# Busy during 30-120 (9:30-11:00), 150-180 (11:30-12:30), 240-420 (13:00-16:00), 450-480 (16:30-17:00)
s.add(Or(
    start_time + 30 <= 30,    # Before 9:30
    And(start_time >= 120, start_time + 30 <= 150),   # 11:00-11:30
    And(start_time >= 180, start_time + 30 <= 240),   # 12:30-13:00
    And(start_time >= 420, start_time + 30 <= 450)    # 16:00-16:30
))

# Find earliest possible time
s.minimize(start_time)

if s.check() == sat:
    m = s.model()
    d = m[day].as_long()
    st = m[start_time].as_long()
    days = ['Monday', 'Tuesday']
    start_h = 9 + st // 60
    start_m = st % 60
    end_h = 9 + (st + 30) // 60
    end_m = (st + 30) % 60
    print(f"{days[d]} {start_h:02d}:{start_m:02d}-{end_h:02d}:{end_m:02d}")
else:
    print("No solution found")