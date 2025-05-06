from z3 import *

s = Optimize()

day = Int('day')
start_time = Int('start_time')

# Meeting must be on Monday
s.add(day == 0)

# Time constraints (minutes since 9:00)
s.add(start_time >= 0)
s.add(start_time + 30 <= 480)  # 30-minute duration

# Define busy blocks for each participant (Monday only)
busy = {
    'Emily': {0: [(60, 90), (420, 450)]},
    'Maria': {0: [(90, 120), (300, 330)]},
    'Carl': {0: [(30, 60), (90, 210), (270, 300), (330, 390), (420, 480)]},
    'David': {0: [(30, 120), (150, 180), (210, 270), (300, 360), (420, 480)]},
    'Frank': {0: [(30, 90), (120, 150), (210, 270), (330, 480)]}
}

# Add availability constraints for each participant
for person, schedule in busy.items():
    for d, blocks in schedule.items():
        for block_start, block_end in blocks:
            s.add(Implies(day == d, Or(
                start_time + 30 <= block_start,
                start_time >= block_end
            )))

# Optimize for earliest time
s.minimize(start_time)

if s.check() == sat:
    m = s.model()
    st = m[start_time].as_long()
    start_h = 9 + st // 60
    start_m = st % 60
    end_h = 9 + (st + 30) // 60
    end_m = (st + 30) % 60
    print(f"Monday {start_h:02d}:{start_m:02d}-{end_h:02d}:{end_m:02d}")
else:
    print("No solution found")