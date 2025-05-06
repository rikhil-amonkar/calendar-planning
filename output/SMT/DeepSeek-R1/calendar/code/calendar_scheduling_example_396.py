from z3 import *

s = Optimize()

start_time = Int('start_time')

# Time constraints (minutes since 9:00)
s.add(start_time >= 0)
s.add(start_time + 30 <= 480)  # 30-minute duration

# Define busy blocks in minutes since 9:00 (Monday only)
busy = {
    'Jack': [(0, 30), (300, 330)],
    'Madison': [(30, 90), (240, 300), (360, 390), (450, 480)],
    'Rachel': [(30, 90), (120, 150), (180, 270), (330, 390), (420, 480)],
    'Douglas': [(0, 150), (180, 450)],
    'Ryan': [(0, 30), (240, 300), (330, 480)]
}

# Add constraints for each participant's busy times (Andrea has none)
for person, blocks in busy.items():
    for block_start, block_end in blocks:
        s.add(Or(
            start_time + 30 <= block_start,
            start_time >= block_end
        ))

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