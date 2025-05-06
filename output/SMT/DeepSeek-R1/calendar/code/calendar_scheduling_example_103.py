from z3 import *

s = Optimize()

start = Int('start')
day = 0  # Fixed to Monday

# Meeting must be 30 minutes within 9:00-17:00 (0-480 minutes)
s.add(start >= 0)
s.add(start + 30 <= 480)

# Define busy intervals in minutes since 9:00
busy = {
    'Diane': [(30, 60), (330, 360)],
    'Jack': [(210, 240), (330, 360)],
    'Eugene': [(0, 60), (90, 150), (180, 330), (360, 450)],
    'Patricia': [(30, 90), (120, 180), (210, 300), (360, 450)]
}

# Add constraints for each person's busy intervals
for person in busy:
    for (block_start, block_end) in busy[person]:
        s.add(Or(start + 30 <= block_start, start >= block_end))

# Optimize for earliest time
s.minimize(start)

if s.check() == sat:
    m = s.model()
    st = m[start].as_long()
    start_h = 9 + st // 60
    start_m = st % 60
    end_h = 9 + (st + 30) // 60
    end_m = (st + 30) % 60
    print(f"Monday {start_h:02d}:{start_m:02d}-{end_h:02d}:{end_m:02d}")
else:
    print("No solution found")