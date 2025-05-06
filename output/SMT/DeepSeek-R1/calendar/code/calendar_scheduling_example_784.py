from z3 import *

s = Optimize()

day = Int('day')
start = Int('start')

# Day constraints: 0=Mon,1=Tue,2=Wed (exclude Monday via Judith's preference)
s.add(Or(day == 1, day == 2))
s.add(start >= 0)
s.add(start + 60 <= 480)  # 1-hour duration within 9:00-17:00

# Judith's Wednesday preference: no meetings before 12:00 (180 minutes)
s.add(If(day == 2, start >= 180, True))

# Convert schedules to minutes since 9:00 for each day
busy = {
    'Judith': {
        0: [(180, 210)],   # Mon 12:00-12:30
        2: [(150, 180)]    # Wed 11:30-12:00
    },
    'Timothy': {
        0: [(30, 60), (90, 150), (210, 300), (390, 480)],       # Mon
        1: [(30, 240), (270, 300), (330, 480)],                 # Tue
        2: [(0, 30), (90, 120), (270, 330), (360, 390), (420, 450)]  # Wed
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