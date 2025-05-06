from z3 import *

s = Optimize()

day = Int('day')
start_time = Int('start_time')

# Days: Monday(0), Tuesday(1)
s.add(day >= 0, day <= 1)
s.add(start_time >= 0)
s.add(start_time + 30 <= 480)  # 30-minute duration

# Convert schedules to minutes since 9:00
busy = {
    'Bobby': {
        0: [(330, 360)],
        1: [(0, 150), (180, 210), (240, 360), (390, 480)]
    },
    'Michael': {
        0: [(0, 60), (90, 270), (300, 360), (390, 480)],
        1: [(0, 90), (120, 150), (180, 300), (360, 420), (450, 480)]
    }
}

# Add constraints for each participant's busy times
for person, schedule in busy.items():
    for d, blocks in schedule.items():
        for block_start, block_end in blocks:
            s.add(Implies(day == d, Or(
                start_time + 30 <= block_start,
                start_time >= block_end
            )))

# Optimize for earliest day and earliest time
optimization_goal = day * 480 + start_time  # Prioritize day first
s.minimize(optimization_goal)

if s.check() == sat:
    m = s.model()
    d = m[day].as_long()
    st = m[start_time].as_long()
    days = ["Monday", "Tuesday"]
    start_h = 9 + st // 60
    start_m = st % 60
    end_h = 9 + (st + 30) // 60
    end_m = (st + 30) % 60
    print(f"{days[d]} {start_h:02d}:{start_m:02d}-{end_h:02d}:{end_m:02d}")
else:
    print("No solution found")