from z3 import *

opt = Optimize()
start = Int('start')
duration = 30  # 30 minutes meeting

# Meeting must be on Monday (fixed day)
opt.add(start >= 0)
opt.add(start + duration <= 480)  # 17:00 = 480 minutes

# Blocked times in minutes since 9:00
emily_blocks = [(60, 90), (420, 450)]
maria_blocks = [(90, 120), (300, 330)]
carl_blocks = [(30, 60), (90, 210), (270, 300), (330, 390), (420, 480)]
david_blocks = [(30, 120), (150, 180), (210, 270), (300, 360), (420, 480)]
frank_blocks = [(30, 90), (120, 150), (210, 270), (330, 480)]

# Add constraints for each person's blocked intervals
for s, e in emily_blocks:
    opt.add(Or(start + duration <= s, start >= e))
for s, e in maria_blocks:
    opt.add(Or(start + duration <= s, start >= e))
for s, e in carl_blocks:
    opt.add(Or(start + duration <= s, start >= e))
for s, e in david_blocks:
    opt.add(Or(start + duration <= s, start >= e))
for s, e in frank_blocks:
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