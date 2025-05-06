from z3 import *

s = Optimize()

start_time = Int('start_time')
s.add(start_time >= 0)
s.add(start_time + 30 <= 480)  # 30-minute duration within 9:00-17:00

# Convert schedules to minutes since 9:00
busy = {
    'Randy': [(0, 90), (120, 390), (420, 480)],
}

# Evelyn has no meetings but can't meet after 13:00 (240 minutes)
s.add(start_time + 30 <= 240)

# Add constraints for Randy's busy times
for block_start, block_end in busy['Randy']:
    s.add(Or(start_time + 30 <= block_start, start_time >= block_end))

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