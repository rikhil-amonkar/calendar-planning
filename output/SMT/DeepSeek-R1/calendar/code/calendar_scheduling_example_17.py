from z3 import Solver, Int, Or, And, Optimize, sat

solver = Optimize()
Start = Int('Start')

# Valid time range considering Helen's preference (must end by 13:30 → 270 minutes)
solver.add(And(0 <= Start, Start + 30 <= 270))

# Find earliest possible time
solver.minimize(Start)

def add_block(start, end):
    solver.add(Or(Start + 30 <= start, Start >= end))

# Margaret's blocked intervals
add_block(0, 60)     # 9:00-10:00
add_block(90, 120)   # 10:30-11:00
add_block(150, 180)  # 11:30-12:00

# Donna's blocked intervals (none in the considered time range)
# No constraints needed

# Helen's blocked intervals
add_block(0, 30)     # 9:00-9:30
add_block(60, 150)   # 10:00-11:30

if solver.check() == sat:
    model = solver.model()
    start_time = model[Start].as_long()
    
    start_h = 9 + start_time // 60
    start_m = start_time % 60
    end_time = start_time + 30
    end_h = 9 + end_time // 60
    end_m = end_time % 60
    
    print(f"Monday {start_h:02d}:{start_m:02d}-{end_h:02d}:{end_m:02d}")
else:
    print("No solution found")