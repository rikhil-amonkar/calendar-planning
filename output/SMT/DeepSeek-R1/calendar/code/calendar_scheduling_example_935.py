from z3 import *

s = Optimize()

day = Int('day')
start_time = Int('start_time')

# Days: Monday(0), Tuesday(1), Wednesday(2), Thursday(3), Friday(4)
s.add(day >= 0, day <= 4)
s.add(start_time >= 0)
s.add(start_time + 30 <= 480)  # 30-minute duration

# Convert schedules to minutes since 9:00
busy = {
    'Terry': {
        0: [(90, 120), (210, 300), (360, 480)],
        1: [(30, 60), (90, 120), (300, 330), (420, 450)],
        2: [(30, 90), (120, 180), (240, 270), (330, 390), (450, 480)],
        3: [(30, 60), (180, 210), (240, 330), (420, 450)],
        4: [(0, 150), (180, 210), (270, 420), (450, 480)]
    },
    'Frances': {
        0: [(30, 120), (150, 240), (300, 330), (360, 420)],
        1: [(0, 30), (60, 90), (120, 180), (240, 330), (390, 450)],
        2: [(30, 60), (90, 120), (150, 420), (450, 480)],
        3: [(120, 210), (330, 480)],
        4: [(30, 90), (120, 210), (240, 420), (450, 480)]
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

# Frances's preference: Avoid Tuesday with penalty
penalty = If(day == 1, 1000, 0)
optimization_goal = day * 1000 + start_time + penalty
s.minimize(optimization_goal)

if s.check() == sat:
    m = s.model()
    d = m[day].as_long()
    st = m[start_time].as_long()
    days = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]
    start_h = 9 + st // 60
    start_m = st % 60
    end_h = 9 + (st + 30) // 60
    end_m = (st + 30) % 60
    print(f"{days[d]} {start_h:02d}:{start_m:02d}-{end_h:02d}:{end_m:02d}")
else:
    print("No solution found")