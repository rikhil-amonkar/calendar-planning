from z3 import *

opt = Optimize()
start = Int('start')
duration = 30  # 30 minutes meeting

# Meeting must be on Monday within 9:00-17:00 (480 minutes)
opt.add(start >= 0)
opt.add(start + duration <= 480)

# Convert blocked times to minutes since 9:00
patrick_blocks = [(0, 30), (60, 90), (270, 300), (420, 450)]          # 9:00-9:30, 10:00-10:30, 13:30-14:00, 16:00-16:30
kayla_blocks = [(210, 270), (360, 390), (420, 450)]                   # 12:30-13:30, 15:00-15:30, 16:00-16:30
carl_blocks = [(90, 120), (180, 210), (240, 270), (330, 480)]        # 10:30-11:00, 12:00-12:30, 13:00-13:30, 14:30-17:00
christian_blocks = [(0, 210), (240, 300), (330, 480)]                # 9:00-12:30, 13:00-14:00, 14:30-17:00

# Add constraints for each person's blocked intervals
for s, e in patrick_blocks:
    opt.add(Or(start + duration <= s, start >= e))
for s, e in kayla_blocks:
    opt.add(Or(start + duration <= s, start >= e))
for s, e in carl_blocks:
    opt.add(Or(start + duration <= s, start >= e))
for s, e in christian_blocks:
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