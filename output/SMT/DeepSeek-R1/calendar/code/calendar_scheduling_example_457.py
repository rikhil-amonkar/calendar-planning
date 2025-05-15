from z3 import Solver, Int, Or, And, Optimize, sat

solver = Optimize()
Start = Int('Start')

# Valid time range for Monday (minutes since 9:00)
solver.add(And(0 <= Start, Start + 30 <= 480))

# Find earliest possible time
solver.minimize(Start)

def add_block(start, end):
    solver.add(Or(Start + 30 <= start, Start >= end))

# Andrea's blocked intervals
add_block(30, 90)    # 9:30-10:30
add_block(270, 330)  # 13:30-14:30

# Ruth's blocked intervals
add_block(210, 240)  # 12:30-13:00
add_block(360, 390)  # 15:00-15:30

# Steven's blocked intervals
add_block(60, 90)    # 10:00-10:30
add_block(120, 150)  # 11:00-11:30
add_block(180, 210)  # 12:00-12:30
add_block(270, 300)  # 13:30-14:00
add_block(360, 420)  # 15:00-16:00

# Kyle's blocked intervals
add_block(0, 30)     # 9:00-9:30
add_block(90, 180)   # 10:30-12:00
add_block(210, 240)  # 12:30-13:00
add_block(270, 360)  # 13:30-15:00
add_block(390, 420)  # 15:30-16:00
add_block(450, 480)  # 16:30-17:00

# Elijah's blocked intervals
add_block(0, 120)    # 9:00-11:00
add_block(150, 240)  # 11:30-13:00
add_block(270, 300)  # 13:30-14:00
add_block(390, 420)  # 15:30-16:00
add_block(450, 480)  # 16:30-17:00

# Lori's blocked intervals
add_block(0, 30)     # 9:00-9:30
add_block(60, 150)   # 10:00-11:30
add_block(180, 270)  # 12:00-13:30
add_block(300, 420)  # 14:00-16:00
add_block(450, 480)  # 16:30-17:00

# Grace has no blocked intervals

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