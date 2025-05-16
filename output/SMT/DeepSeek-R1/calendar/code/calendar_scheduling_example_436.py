from z3 import *

opt = Optimize()
start = Int('start')
duration = 30  # Meeting duration in minutes

opt.add(start >= 0)
opt.add(start + duration <= 480)  # 17:00 = 480 minutes from 9:00

# Define blocked times in minutes since 9:00 for each participant
blocked = {
    'Patrick': [(270, 300), (330, 360)],
    'Shirley': [(0, 30), (120, 150), (180, 210), (330, 360), (420, 480)],
    'Jeffrey': [(0, 30), (90, 120), (150, 180), (240, 270), (420, 480)],
    'Gloria': [(150, 180), (360, 390)],
    'Nathan': [(0, 30), (90, 180), (300, 480)],
    'Angela': [(0, 30), (60, 120), (210, 360), (390, 450)],
    'David': [(0, 30), (60, 90), (120, 300), (330, 450)]
}

# Add constraints for all blocked intervals
for intervals in blocked.values():
    for b_start, b_end in intervals:
        opt.add(Or(start + duration <= b_start, start >= b_end))

# Find the earliest possible time
opt.minimize(start)

if opt.check() == sat:
    m = opt.model()
    start_val = m[start].as_long()
    hours = 9 + start_val // 60
    minutes = start_val % 60
    end_h = 9 + (start_val + duration) // 60
    end_m = (start_val + duration) % 60
    print(f"Monday {hours:02d}:{minutes:02d}-{end_h:02d}:{end_m:02d}")
else:
    print("No valid slot found")