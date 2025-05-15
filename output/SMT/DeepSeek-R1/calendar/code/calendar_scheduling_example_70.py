from z3 import *

opt = Optimize()
start = Int('start')
duration = 30  # 30 minutes meeting

# Meeting must be on Monday within 9:00-17:00 (480 minutes)
opt.add(start >= 0)
opt.add(start + duration <= 480)

# Convert blocked times to minutes since 9:00
denise_blocks = [(180, 210), (390, 420)]  # 12:00-12:30, 15:30-16:00
natalie_blocks = [(0, 150), (180, 240), (300, 330), (360, 480)]  # 9:00-11:30, 12:00-13:00, 14:00-14:30, 15:00-17:00

# Add constraints for blocked intervals (Angela has none)
for s, e in denise_blocks:
    opt.add(Or(start + duration <= s, start >= e))
for s, e in natalie_blocks:
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