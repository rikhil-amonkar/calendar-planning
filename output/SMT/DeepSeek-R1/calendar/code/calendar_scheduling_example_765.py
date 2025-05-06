from z3 import *

s = Optimize()

day = Int('day')
start = Int('start')

# Day constraints: 0=Monday, 2=Wednesday (Tuesday is fully busy for Joyce)
s.add(Or(day == 0, day == 2))
s.add(start >= 0)
s.add(start + 30 <= 480)  # 30-minute duration within 9:00-17:00

# Joyce's preference: no meetings on Monday before 12:00 (180 minutes)
s.add(If(day == 0, start >= 180, True))

# Convert schedules to minutes since 9:00 for each day
busy = {
    'Joshua': {
        0: [(360, 390)],                 # Mon 15:00-15:30
        2: []                             # Wed free
    },
    'Joyce': {
        0: [(0, 30), (60, 120), (150, 210), (240, 360), (390, 480)],  # Mon
        2: [(0, 30), (60, 120), (210, 390), (420, 450)]               # Wed
    }
}

# Add constraints for each participant's busy times on selected day
for person in busy:
    for d in busy[person]:
        for block_start, block_end in busy[person][d]:
            s.add(If(day == d,
                    Or(start + 30 <= block_start, start >= block_end),
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
    end_h = 9 + (st + 30) // 60
    end_m = (st + 30) % 60
    print(f"{days[d]} {start_h:02d}:{start_m:02d}-{end_h:02d}:{end_m:02d}")
else:
    print("No solution found")