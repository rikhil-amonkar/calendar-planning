from z3 import *

opt = Optimize()
start = Int('start')
duration = 30  # 30 minutes meeting

# Meeting must be on Monday, within 9:00-17:00 (480 minutes)
opt.add(start >= 0)
opt.add(start + duration <= 480)

# Blocked times in minutes since 9:00 for each participant (except Ronald)
stephen_blocks = [(60, 90), (180, 210)]
brittany_blocks = [(120, 150), (270, 300), (390, 420), (450, 480)]
dorothy_blocks = [(0, 30), (60, 90), (120, 210), (240, 360), (390, 480)]
rebecca_blocks = [(30, 90), (120, 150), (180, 210), (240, 480)]
jordan_blocks = [(0, 30), (60, 120), (150, 180), (240, 360), (390, 450)]

# Add constraints for each person's blocked intervals
for s, e in stephen_blocks:
    opt.add(Or(start + duration <= s, start >= e))
for s, e in brittany_blocks:
    opt.add(Or(start + duration <= s, start >= e))
for s, e in dorothy_blocks:
    opt.add(Or(start + duration <= s, start >= e))
for s, e in rebecca_blocks:
    opt.add(Or(start + duration <= s, start >= e))
for s, e in jordan_blocks:
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