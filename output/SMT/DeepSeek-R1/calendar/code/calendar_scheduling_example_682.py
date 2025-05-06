from z3 import *

s = Optimize()

day = Int('day')
start_time = Int('start_time')

# Nathan can't meet on Monday, Amanda avoids Tuesday after 11:00
s.add(day == 1)  # Only Tuesday allowed

# Time constraints (minutes since 9:00)
s.add(start_time >= 0)
s.add(start_time + 30 <= 480)

# Amanda's Tuesday constraints (busy times + preference)
amanda_busy = [(0, 30), (60, 90), (150, 180)]
s.add([Or(start_time + 30 <= bs, start_time >= be) for (bs, be) in amanda_busy])
s.add(start_time + 30 <= 120)  # End by 11:00

# Nathan's Tuesday busy times
nathan_busy = [(0, 90), (120, 240)]
s.add([Or(start_time + 30 <= bs, start_time >= be) for (bs, be) in nathan_busy])

# Find earliest time
s.minimize(start_time)

if s.check() == sat:
    m = s.model()
    st = m[start_time].as_long()
    start_h = 9 + st // 60
    start_m = st % 60
    end_h = 9 + (st + 30) // 60
    end_m = (st + 30) % 60
    print(f"Tuesday {start_h:02d}:{start_m:02d}-{end_h:02d}:{end_m:02d}")
else:
    print("No solution found")