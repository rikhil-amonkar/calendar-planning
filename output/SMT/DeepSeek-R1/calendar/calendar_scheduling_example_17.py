from z3 import *

solver = Solver()

# Define the start time variable in minutes from 9:00
S = Int('S')
solver.add(S >= 0, S + 30 <= 480)  # Work hours constraint (9:00-17:00)

# Helen's constraint: meeting must end by 13:30 (270 minutes from 9:00)
solver.add(S + 30 <= 270)

# Margaret's blocked times: 9:00-10:00 (0-60), 10:30-11:00 (90-120), 
# 11:30-12:00 (150-180), 13:00-13:30 (240-270), 15:00-15:30 (360-390)
margaret_blocks = [(0, 60), (90, 120), (150, 180), (240, 270), (360, 390)]
for start, end in margaret_blocks:
    solver.add(Or(S + 30 <= start, S >= end))

# Helen's blocked times: 9:00-9:30 (0-30), 10:00-11:30 (60-150), 
# 13:00-14:00 (240-300), 14:30-15:00 (330-360), 15:30-17:00 (390-480)
helen_blocks = [(0, 30), (60, 150), (240, 300), (330, 360), (390, 480)]
for start, end in helen_blocks:
    solver.add(Or(S + 30 <= start, S >= end))

# Donna's blocked times: 14:30-15:00 (330-360), 16:00-16:30 (420-450)
# Constraints automatically satisfied due to Helen's 13:30 end time limit
donna_blocks = [(330, 360), (420, 450)]
for start, end in donna_blocks:
    solver.add(Or(S + 30 <= start, S >= end))

if solver.check() == sat:
    m = solver.model()
    start_min = m[S].as_long()
    hours = 9 + start_min // 60
    minutes = start_min % 60
    print(f"Meeting starts at {hours}:{minutes:02d}")
else:
    print("No valid time found")