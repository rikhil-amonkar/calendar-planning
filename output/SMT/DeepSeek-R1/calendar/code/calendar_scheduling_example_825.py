from z3 import *

s = Optimize()

day = Int('day')
start = Int('start')

# Day constraints: 1=Tue,3=Thu (Monday and Wednesday excluded)
s.add(Or(day == 1, day == 3))
s.add(start >= 0)
s.add(start + 60 <= 480)  # 1-hour duration within 9:00-17:00

# Convert schedules to minutes since 9:00 for each day
busy = {
    'Laura': {
        0: [(90, 120), (150, 180), (270, 330), (420, 480)],
        1: [(30, 60), (120, 150), (240, 270), (330, 360), (420, 480)],
        3: [(90, 120), (180, 270), (360, 390), (420, 450)]
    },
    'Philip': {
        0: [(0, 480)],
        1: [(0, 120), (150, 180), (240, 270), (300, 330), (360, 450)],
        3: [(0, 90), (120, 210), (240, 480)]
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
    days = ['Monday', 'Tuesday', 'Wednesday', 'Thursday']
    start_h = 9 + st // 60
    start_m = st % 60
    end_h = 9 + (st + 60) // 60
    end_m = (st + 60) % 60
    print(f"{days[d]} {start_h:02d}:{start_m:02d}-{end_h:02d}:{end_m:02d}")
else:
    print("No solution found")