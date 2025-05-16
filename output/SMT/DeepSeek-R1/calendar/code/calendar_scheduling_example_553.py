from z3 import *

opt = Optimize()
start = Int('start')
duration = 30  # 30 minutes meeting

# Meeting must be on Monday within 9:00-17:00 (480 minutes)
opt.add(start >= 0)
opt.add(start + duration <= 480)

# Convert blocked times to minutes since 9:00
eric_blocks = [(180, 240), (300, 360)]               # 12:00-13:00, 14:00-15:00
henry_blocks = [(30, 60), (90, 120), (150, 210), (240, 270), (330, 360), (420, 480)]  # Henry's blocked intervals

# Add constraints for blocked intervals
for s, e in eric_blocks:
    opt.add(Or(start + duration <= s, start >= e))
for s, e in henry_blocks:
    opt.add(Or(start + duration <= s, start >= e))

# Henry's preference: meeting must end by 10:00 (60 minutes from 9:00)
opt.add(start + duration <= 60)

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