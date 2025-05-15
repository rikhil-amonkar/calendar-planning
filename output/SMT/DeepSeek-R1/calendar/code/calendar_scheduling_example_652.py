from z3 import Solver, Int, Or, Optimize, sat

solver = Optimize()
Start = Int('Start')

# Basic constraints: 30-minute meeting within 9:00-17:00 (480 minutes)
solver.add(Start >= 0)
solver.add(Start + 30 <= 480)  # Ensure meeting ends by 17:00

# Function to add blocked time constraints
def add_blocks(blocks):
    for block_start, block_end in blocks:
        solver.add(Or(Start + 30 <= block_start, Start >= block_end))

# Jesse's Tuesday blocked times (minutes since 9:00):
# 9:00-9:30 (0-30), 13:00-13:30 (240-270), 14:00-15:00 (300-360)
add_blocks([(0, 30), (240, 270), (300, 360)])

# Lawrence's Tuesday blocked times:
# 9:30-10:30 (30-90), 11:30-12:30 (150-180), 13:00-13:30 (240-270),
# 14:30-15:00 (330-360), 15:30-16:30 (390-450). Also, can't meet after 16:30 (Start+30 <=450)
solver.add(Start + 30 <= 450)  # Lawrence's Tuesday end-time constraint
add_blocks([(30, 90), (150, 180), (240, 270), (330, 360), (390, 450)])

# Find earliest possible time
solver.minimize(Start)

if solver.check() == sat:
    model = solver.model()
    start_min = model[Start].as_long()
    start_h = 9 + start_min // 60
    start_m = start_min % 60
    end_min = start_min + 30
    end_h = 9 + end_min // 60
    end_m = end_min % 60
    print(f"Tuesday {start_h:02d}:{start_m:02d}-{end_h:02d}:{end_m:02d}")
else:
    print("No solution found")