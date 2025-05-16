from z3 import Solver, Int, Or, And, Optimize, sat

solver = Optimize()
Start = Int('Start')

# Valid time range for Monday (minutes since 9:00, 480 = 17:00)
solver.add(And(0 <= Start, Start + 60 <= 480))

# Find earliest possible time
solver.minimize(Start)

def add_block(start, end):
    solver.add(Or(Start + 60 <= start, Start >= end))

# Stephanie's blocked intervals
add_block(60, 90)    # 10:00-10:30
add_block(420, 450)  # 16:00-16:30

# Cheryl's blocked intervals
add_block(60, 90)    # 10:00-10:30
add_block(150, 180)  # 11:30-12:00
add_block(270, 300)  # 13:30-14:00
add_block(450, 480)  # 16:30-17:00

# Bradley's blocked intervals
add_block(30, 60)    # 9:30-10:00
add_block(90, 150)   # 10:30-11:30
add_block(270, 300)  # 13:30-14:00
add_block(330, 360)  # 14:30-15:00
add_block(390, 480)  # 15:30-17:00

# Steven's blocked intervals
add_block(0, 180)    # 9:00-12:00
add_block(240, 270)  # 13:00-13:30
add_block(330, 480)  # 14:30-17:00

if solver.check() == sat:
    model = solver.model()
    start_time = model[Start].as_long()
    
    start_h = 9 + start_time // 60
    start_m = start_time % 60
    end_time = start_time + 60
    end_h = 9 + end_time // 60
    end_m = end_time % 60
    
    print(f"Monday {start_h:02d}:{start_m:02d}-{end_h:02d}:{end_m:02d}")
else:
    print("No solution found")