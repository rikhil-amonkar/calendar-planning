from z3 import *

s = Optimize()

day = Int('day')
start_time = Int('start_time')

# Days: Monday(0) to Friday(4)
s.add(day >= 0, day <= 4)

# Time constraints (minutes since 9:00)
s.add(start_time >= 0)
s.add(start_time + 60 <= 480)  # 1-hour duration

# Convert schedules to minutes since 9:00
busy = {
    'Brian': {
        0: [(30, 60), (150, 270), (330, 360)],
        1: [(0, 30)],
        2: [(150, 240), (390, 480)],
        3: [(120, 150), (240, 270), (390, 480)],
        4: [(30, 60), (90, 120), (240, 270), (360, 420), (390, 480)]
    },
    'Julia': {
        0: [(0, 60), (120, 150), (330, 360)],
        1: [(240, 300), (420, 450)],
        2: [(0, 150), (180, 210), (240, 480)],
        3: [(0, 90), (120, 480)],
        4: [(0, 60), (90, 150), (210, 300), (330, 360), (390, 420)]
    }
}

# Add availability constraints for each participant
for person, schedule in busy.items():
    for d, blocks in schedule.items():
        for block_start, block_end in blocks:
            s.add(Implies(day == d, Or(
                start_time + 60 <= block_start,
                start_time >= block_end
            )))

# Brian's preference: Avoid Monday by adding weight to day 0
# We minimize (day_penalty * 1000 + start_time) to prioritize earliest time
day_penalty = If(day == 0, 1, 0)  # Penalize Monday with higher weight
s.minimize(day_penalty * 1000 + start_time)

if s.check() == sat:
    m = s.model()
    d = m[day].as_long()
    st = m[start_time].as_long()
    days = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]
    start_h = 9 + st // 60
    start_m = st % 60
    end_h = 9 + (st + 60) // 60
    end_m = (st + 60) % 60
    print(f"{days[d]} {start_h:02d}:{start_m:02d}-{end_h:02d}:{end_m:02d}")
else:
    print("No solution found")