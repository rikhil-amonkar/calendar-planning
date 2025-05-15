from z3 import *

opt = Optimize()
start = Int('start')
duration = 60  # 1 hour meeting

# Meeting must be on Monday within 9:00-17:00 (480 minutes)
opt.add(start >= 0)
opt.add(start + duration <= 480)

# Convert blocked times to minutes since 9:00
olivia_blocks = [(210, 270), (330, 360), (450, 480)]    # 12:30-13:30, 14:30-15:00, 16:30-17:00
virginia_blocks = [(0, 60), (150, 420), (450, 480)]      # 9:00-10:00, 11:30-16:00, 16:30-17:00
paul_blocks = [(0, 30), (120, 150), (240, 300), (330, 420), (450, 480)]  # 9:00-9:30, 11:00-11:30, 13:00-14:00, 14:30-16:00, 16:30-17:00

# Add constraints for blocked intervals (Anna has none)
for s, e in olivia_blocks:
    opt.add(Or(start + duration <= s, start >= e))
for s, e in virginia_blocks:
    opt.add(Or(start + duration <= s, start >= e))
for s, e in paul_blocks:
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