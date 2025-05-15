from z3 import Solver, Int, Or, And, Optimize, If, sat

solver = Optimize()
Start = Int('Start')

# Valid time range for Monday (0-450 minutes from 9:00)
solver.add(And(0 <= Start, Start + 30 <= 480))

# Penalize times before 14:30 (330 minutes)
penalty = If(Start < 330, 1, 0)
solver.minimize(penalty)
solver.minimize(Start)  # Then find earliest time

def add_block(start, end):
    solver.add(Or(Start + 30 <= start, Start >= end))

# Adam's blocked (14:00-15:00 → 300-360)
add_block(300, 360)

# John's blocks
add_block(240, 270)   # 13:00-13:30
add_block(300, 330)   # 14:00-14:30
add_block(390, 420)   # 15:30-16:00
add_block(450, 480)   # 16:30-17:00

# Stephanie's blocks
add_block(30, 60)     # 9:30-10:00
add_block(90, 120)    # 10:30-11:00
add_block(150, 420)   # 11:30-16:00
add_block(450, 480)   # 16:30-17:00

# Anna's blocks
add_block(30, 60)     # 9:30-10:00
add_block(180, 210)   # 12:00-12:30
add_block(240, 390)   # 13:00-15:30
add_block(450, 480)   # 16:30-17:00

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