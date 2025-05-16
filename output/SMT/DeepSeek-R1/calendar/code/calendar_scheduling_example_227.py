from z3 import *

opt = Optimize()
start = Int('start')
duration = 30  # 30 minutes meeting

# Meeting must be on Monday within 9:00-17:00 (480 minutes)
opt.add(start >= 0)
opt.add(start + duration <= 480)

# David's constraint: no meetings before 14:00 (300 minutes since 9:00)
opt.add(start >= 300)

# Blocked times in minutes since 9:00
david_blocks = [(150, 180), (330, 360)]  # 11:30-12:00, 14:30-15:00
douglas_blocks = [(30, 60), (150, 180), (240, 270), (330, 360)]  # 9:30-10:00, 11:30-12:00, 13:00-13:30, 14:30-15:00
ralph_blocks = [(0, 30), (60, 120), (150, 210), (270, 360), (390, 420), (450, 480)]  # 9:00-9:30, 10:00-11:00, 11:30-12:30, 13:30-15:00, 15:30-16:00, 16:30-17:00
jordan_blocks = [(0, 60), (180, 210), (240, 270), (330, 360), (390, 480)]  # 9:00-10:00, 12:00-12:30, 13:00-13:30, 14:30-15:00, 15:30-17:00

# Add constraints for each person's blocked intervals (Natalie has none)
for s, e in david_blocks:
    opt.add(Or(start + duration <= s, start >= e))
for s, e in douglas_blocks:
    opt.add(Or(start + duration <= s, start >= e))
for s, e in ralph_blocks:
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