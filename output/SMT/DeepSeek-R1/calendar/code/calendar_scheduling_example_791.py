from z3 import *

s = Optimize()

day = Int('day')
start_time = Int('start_time')

# Days: Monday(0), Tuesday(1), Wednesday(2)
s.add(day >= 0, day <= 2)

# Time constraints (minutes since 9:00)
s.add(start_time >= 0)
s.add(start_time + 30 <= 480)  # 30-minute duration

# Convert schedules to minutes since 9:00
busy = {
    'Nicole': {
        0: [(0, 30), (240, 270), (330, 390)],
        1: [(0, 30), (150, 270), (330, 390)],
        2: [(60, 120), (210, 360), (420, 480)]
    },
    'Ruth': {
        0: [(0, 480)],
        1: [(0, 480)],
        2: [(0, 90), (120, 150), (180, 210), (270, 390), (420, 450)]
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

# Ruth's constraint: Wednesday meetings must end by 13:30 (270 minutes)
s.add(Implies(day == 2, start_time + 30 <= 270))

# Optimize for earliest time (day priority first, then start time)
s.minimize(day * 1000 + start_time)

if s.check() == sat:
    m = s.model()
    d = m[day].as_long()
    st = m[start_time].as_long()
    days = ["Monday", "Tuesday", "Wednesday"]
    start_h = 9 + st // 60
    start_m = st % 60
    end_h = 9 + (st + 30) // 60
    end_m = (st + 30) % 60
    print(f"{days[d]} {start_h:02d}:{start_m:02d}-{end_h:02d}:{end_m:02d}")
else:
    print("No solution found")