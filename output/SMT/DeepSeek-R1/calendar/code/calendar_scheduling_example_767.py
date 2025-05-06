from z3 import *

s = Optimize()

day = Int('day')
start = Int('start')

# Day constraints: 0=Monday,1=Tuesday,2=Wednesday
s.add(Or(day == 0, day == 1, day == 2))
s.add(start >= 0)
s.add(start + 60 <= 480)  # 1-hour duration within 9:00-17:00

# Convert schedules to minutes since 9:00 for each day
busy = {
    'Martha': {
        0: [(420, 480)],                # Mon 16:00-17:00
        1: [(360, 390)],                 # Tue 15:00-15:30
        2: [(60, 120), (300, 330)]       # Wed 10:00-11:00,14:00-14:30
    },
    'Beverly': {
        0: [(0, 270), (300, 480)],       # Mon 9:00-13:30,14:00-17:00
        1: [(0, 480)],                   # Tue all day
        2: [(30, 390), (450, 480)]       # Wed 9:30-15:30,16:30-17:00
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
    days = ['Monday', 'Tuesday', 'Wednesday']
    start_h = 9 + st // 60
    start_m = st % 60
    end_h = 9 + (st + 60) // 60
    end_m = (st + 60) % 60
    print(f"{days[d]} {start_h:02d}:{start_m:02d}-{end_h:02d}:{end_m:02d}")
else:
    print("No solution found")