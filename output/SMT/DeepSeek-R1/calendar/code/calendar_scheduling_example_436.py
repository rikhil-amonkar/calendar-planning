from z3 import *

s = Optimize()

start_time = Int('start_time')

# Convert all times to minutes since 9:00 (0 = 9:00, 480 = 17:00)
s.add(start_time >= 0)
s.add(start_time + 30 <= 480)  # Meeting must end by 17:00

# Define busy blocks for each participant in minutes
busy = {
    'Patrick': [(210, 240), (270, 300)],
    'Shirley': [(0, 30), (120, 150), (180, 210), (270, 300), (420, 480)],
    'Jeffrey': [(0, 30), (90, 120), (150, 180), (240, 270), (420, 480)],
    'Gloria': [(150, 180), (300, 330)],
    'Nathan': [(0, 30), (90, 180), (300, 480)],
    'Angela': [(0, 30), (60, 120), (210, 300), (330, 390)],
    'David': [(0, 30), (60, 90), (120, 300), (330, 420)]
}

# Add constraints for each participant's busy times
for person, blocks in busy.items():
    for block_start, block_end in blocks:
        s.add(Or(
            start_time + 30 <= block_start,
            start_time >= block_end
        ))

# Find earliest possible time
s.minimize(start_time)

if s.check() == sat:
    m = s.model()
    st = m[start_time].as_long()
    start_h = 9 + st // 60
    start_m = st % 60
    end_h = 9 + (st + 30) // 60
    end_m = (st + 30) % 60
    print(f"Monday {start_h:02d}:{start_m:02d}-{end_h:02d}:{end_m:02d}")
else:
    print("No solution found")