from z3 import *

s = Optimize()

day = Int('day')
start_time = Int('start_time')

# Days: Monday(0), Tuesday(1), Wednesday(2), Thursday(3), Friday(4)
s.add(day >= 0, day <= 4)
s.add(start_time >= 0)
s.add(start_time + 60 <= 480)  # 1-hour duration

# Convert schedules to minutes since 9:00
busy = {
    'Diane': {
        0: [(180, 210), (360, 390)],
        1: [(60, 120), (150, 180), (210, 240), (420, 480)],
        2: [(0, 30), (330, 360), (450, 480)],
        3: [(390, 450)],
        4: [(30, 150), (330, 360), (420, 480)]
    },
    'Matthew': {
        0: [(0, 60), (90, 480)],
        1: [(0, 480)],
        2: [(0, 120), (180, 330), (420, 480)],
        3: [(0, 420)],
        4: [(0, 480)]
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

# Matthew's preference: Avoid Wednesday before 12:30 (210 minutes)
penalty = If(And(day == 2, start_time < 210), 1000, 0)
optimization_goal = day * 480 + start_time + penalty
s.minimize(optimization_goal)

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