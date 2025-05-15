from z3 import *

opt = Optimize()
start = Int('start')
duration = 30  # 30 minutes meeting

# Meeting must be on Monday and end by 15:00 (360 minutes since 9:00)
opt.add(start >= 0)
opt.add(start + duration <= 360)

# Convert blocked times to minutes since 9:00
christine_blocks = [(120, 150), (360, 390)]  # 11:00-11:30, 15:00-15:30
helen_blocks = [(30, 90), (120, 150), (180, 210), (270, 420), (450, 480)]  # Helen's blocks

# Add constraints for both participants
for s, e in christine_blocks:
    opt.add(Or(start + duration <= s, start >= e))
for s, e in helen_blocks:
    opt.add(Or(start + duration <= s, start >= e))

# Optimize for earliest possible time
opt.minimize(start)

if opt.check() == sat:
    m = opt.model()
    st = m[start].as_long()
    start_h = 9 + st // 60
    start_m = st % 60
    end_h = 9 + (st + duration) // 60
    end_m = (st + duration) % 60
    print(f"Monday {start_h:02d}:{start_m:02d}-{end_h:02d}:{end_m:02d}")
else:
    print("No valid slot found")