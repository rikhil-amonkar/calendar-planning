from z3 import Solver, Int, Or, sat

solver = Solver()
Start = Int('Start')

# All constraints are for Monday only
solver.add(Start >= 0)
solver.add(Start + 60 <= 480)  # 1-hour meeting within 9:00-17:00

# Ryan's blocked times (minutes since 9:00)
ryan_blocks = [(0, 30), (210, 240)]
for (block_start, block_end) in ryan_blocks:
    solver.add(Or(Start + 60 <= block_start, Start >= block_end))

# Denise's blocked times and preferences
denise_blocks = [(30, 90), (180, 240), (330, 450)]
for (block_start, block_end) in denise_blocks:
    solver.add(Or(Start + 60 <= block_start, Start >= block_end))
solver.add(Start + 60 <= 210)  # Must end by 12:30

# Find earliest possible time
if solver.check() == sat:
    model = solver.model()
    start_min = model[Start].as_long()
    
    # Calculate time strings
    start_h = 9 + start_min // 60
    start_m = start_min % 60
    end_min = start_min + 60
    end_h = 9 + end_min // 60
    end_m = end_min % 60
    
    print(f"Monday {start_h:02d}:{start_m:02d}-{end_h:02d}:{end_m:02d}")
else:
    print("No solution found")