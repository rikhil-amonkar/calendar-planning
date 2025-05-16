from z3 import Solver, Int, Or, And, Optimize, sat

solver = Optimize()
Start = Int('Start')

# Valid time range for Monday (0-450 minutes from 9:00)
solver.add(And(0 <= Start, Start + 30 <= 480))

# No preferences except earliest possible time
solver.minimize(Start)

def add_block(start, end):
    solver.add(Or(Start + 30 <= start, Start >= end))

# Samuel's blocked intervals (minutes since 9:00)
add_block(0, 90)     # 9:00-10:30
add_block(150, 180)  # 11:30-12:00
add_block(240, 270)  # 13:00-13:30
add_block(300, 420)  # 14:00-16:00
add_block(450, 480)  # 16:30-17:00

# Andrew and Grace have no blocks - no constraints needed

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