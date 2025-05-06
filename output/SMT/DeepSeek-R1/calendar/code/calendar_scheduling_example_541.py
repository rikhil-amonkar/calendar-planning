from z3 import *

s = Optimize()

start_time = Int('start_time')

# Time constraints (minutes since 9:00)
s.add(start_time >= 0)
s.add(start_time + 60 <= 480)  # 1-hour duration

# Define busy blocks in minutes since 9:00
busy = {
    'Kayla': [(60, 90), (270, 360)],
    'Rebecca': [(0, 240), (270, 360), (390, 420)]
}

# Add constraints for each participant's busy times
for person, blocks in busy.items():
    for block_start, block_end in blocks:
        s.add(Or(
            start_time + 60 <= block_start,
            start_time >= block_end
        ))

# Optimize for earliest time
s.minimize(start_time)

if s.check() == sat:
    m = s.model()
    st = m[start_time].as_long()
    start_h = 9 + st // 60
    start_m = st % 60
    end_h = 9 + (st + 60) // 60
    end_m = (st + 60) % 60
    print(f"Monday {start_h:02d}:{start_m:02d}-{end_h:02d}:{end_m:02d}")
else:
    print("No solution found")