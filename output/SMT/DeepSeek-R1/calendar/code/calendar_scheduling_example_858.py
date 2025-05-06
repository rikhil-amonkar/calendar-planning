from z3 import *

s = Optimize()

day = Int('day')
start_time = Int('start_time')

# Days: Monday(0), Tuesday(1), Wednesday(2), Thursday(3)
s.add(Or(day == 0, day == 1, day == 2, day == 3))

# Time constraints (minutes since 9:00)
s.add(start_time >= 0)
s.add(start_time + 60 <= 480)  # 1-hour duration

# Convert schedules to minutes since 9:00
busy = {
    'Carl': {
        0: [(120, 150)],
        1: [(330, 360)],
        2: [(60, 150), (240, 270)],
        3: [(270, 300), (420, 450)]
    },
    'Margaret': {
        0: [(0, 90), (120, 480)],
        1: [(30, 180), (270, 300), (390, 480)],
        2: [(30, 180), (210, 240), (270, 330), (360, 480)],
        3: [(60, 180), (210, 300), (330, 480)]
    }
}

# Add constraints for each participant's busy times
for person, schedule in busy.items():
    for d, blocks in schedule.items():
        for block_start, block_end in blocks:
            s.add(Implies(day == d, Or(
                start_time + 60 <= block_start,
                start_time >= block_end
            )))

# Carl's preference: Avoid Thursday by adding penalty weight
day_penalty = If(day == 3, 1, 0)  # Penalize Thursday
s.minimize(day_penalty * 1000 + start_time)

if s.check() == sat:
    m = s.model()
    d = m[day].as_long()
    st = m[start_time].as_long()
    days = ["Monday", "Tuesday", "Wednesday", "Thursday"]
    start_h = 9 + st // 60
    start_m = st % 60
    end_h = 9 + (st + 60) // 60
    end_m = (st + 60) % 60
    print(f"{days[d]} {start_h:02d}:{start_m:02d}-{end_h:02d}:{end_m:02d}")
else:
    print("No solution found")