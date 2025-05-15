from z3 import Solver, Int, Or, And, Optimize, sat

solver = Optimize()
Start = Int('Start')

# Apply Margaret's time constraint (start after 14:30) and valid work hours
solver.add(And(330 <= Start, Start + 30 <= 480))  # 330 = 14:30 in minutes from 9:00

# Optimize for earliest possible time
solver.minimize(Start)

def add_block(start, end):
    solver.add(Or(Start + 30 <= start, Start >= end))

# Shirley's blocked intervals
add_block(90, 120)   # 10:30-11:00
add_block(180, 210)  # 12:00-12:30

# Jacob's blocked intervals
add_block(0, 30)     # 9:00-9:30
add_block(60, 90)    # 10:00-10:30
add_block(120, 150)  # 11:00-11:30
add_block(210, 270)  # 12:30-13:30
add_block(330, 360)  # 14:30-15:00

# Stephen's blocked intervals
add_block(150, 180)  # 11:30-12:00
add_block(210, 240)  # 12:30-13:00

# Margaret's blocked intervals
add_block(0, 30)     # 9:00-9:30
add_block(90, 210)   # 10:30-12:30
add_block(240, 270)  # 13:00-13:30
add_block(360, 390)  # 15:00-15:30
add_block(450, 480)  # 16:30-17:00

# Mason's blocked intervals
add_block(0, 60)     # 9:00-10:00
add_block(90, 120)   # 10:30-11:00
add_block(150, 210)  # 11:30-12:30
add_block(240, 270)  # 13:00-13:30
add_block(300, 330)  # 14:00-14:30
add_block(450, 480)  # 16:30-17:00

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