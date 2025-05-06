from z3 import *

s = Optimize()

day = Int('day')
start = Int('start')

# Day constraints: 0=Monday,1=Tuesday
s.add(Or(day == 0, day == 1))
s.add(start >= 0)
s.add(start + 60 <= 480)  # 1-hour duration within 9:00-17:00

# Convert schedules to minutes since 9:00 for each day
busy = {
    'Gary': {
        0: [(30, 60), (120, 240), (300, 330), (450, 480)],  # Mon
        1: [(0, 30), (90, 120), (330, 420)]                  # Tue
    },
    'David': {
        0: [(0, 30), (60, 240), (330, 450)],                  # Mon
        1: [(0, 30), (60, 90), (120, 210), (240, 330), (360, 420), (450, 480)]  # Tue
    }
}

# Add constraints for each participant's busy times on selected day
for person in busy:
    for d in busy[person]:
        for block_start, block_end in busy[person][d]:
            s.add(If(day == d,
                    Or(start + 60 <= block_start, start >= block_end),
                    True))

# Optimize for earliest day and earliest time
s.minimize(day * 1000 + start)

if s.check() == sat:
    m = s.model()
    d = m[day].as_long()
    st = m[start].as_long()
    days = ['Monday', 'Tuesday']
    start_h = 9 + st // 60
    start_m = st % 60
    end_h = 9 + (st + 60) // 60
    end_m = (st + 60) % 60
    print(f"{days[d]} {start_h:02d}:{start_m:02d}-{end_h:02d}:{end_m:02d}")
else:
    print("No solution found")