from z3 import *

opt = Optimize()
start = Int('start')
duration = 30  # 30 minutes meeting

# Meeting must be on Monday
opt.add(start >= 0)
opt.add(start + duration <= 480)  # 17:00 = 480 minutes

# Melissa's preference: meeting must end by 14:00 (300 minutes)
opt.add(start + duration <= 300)

# Blocked times in minutes since 9:00
jeffrey_blocks = [(30, 60), (90, 120)]
virginia_blocks = [(0, 30), (60, 90), (330, 360), (420, 450)]
melissa_blocks = [(0, 150), (180, 210), (240, 360), (420, 480)]

# Add constraints for each person's blocked intervals
for s, e in jeffrey_blocks:
    opt.add(Or(start + duration <= s, start >= e))
for s, e in virginia_blocks:
    opt.add(Or(start + duration <= s, start >= e))
for s, e in melissa_blocks:
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