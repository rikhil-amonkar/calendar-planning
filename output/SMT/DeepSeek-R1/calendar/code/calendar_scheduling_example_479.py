from z3 import Solver, Int, Or, Optimize, sat

solver = Optimize()
Start = Int('Start')

# Convert time to minutes since 9:00 (0-480)
solver.add(Start >= 0)
solver.add(Start + 60 <= 480)  # Must end by 17:00

# Function to add blocked time ranges
def add_block(start, end):
    solver.add(Or(Start + 60 <= start, Start >= end))

# Joshua's blocked times (minutes from 9:00)
add_block(120, 210)   # 11:00-12:30
add_block(270, 330)   # 13:30-14:30
add_block(450, 480)   # 16:30-17:00

# Jerry's blocked times
add_block(0, 30)      # 9:00-9:30
add_block(90, 180)    # 10:30-12:00
add_block(210, 240)   # 12:30-13:00
add_block(270, 300)   # 13:30-14:00
add_block(330, 360)   # 14:30-15:00
add_block(390, 420)   # 15:30-16:00

# Jesse's blocked times
add_block(0, 30)      # 9:00-9:30
add_block(90, 180)    # 10:30-12:00
add_block(210, 240)   # 12:30-13:00
add_block(330, 360)   # 14:30-15:00
add_block(390, 450)   # 15:30-16:30

# Kenneth's blocked times
add_block(90, 210)    # 10:30-12:30
add_block(270, 300)   # 13:30-14:00
add_block(330, 360)   # 14:30-15:00
add_block(390, 420)   # 15:30-16:00
add_block(450, 480)   # 16:30-17:00

# Find earliest possible time
solver.minimize(Start)

if solver.check() == sat:
    model = solver.model()
    start_minutes = model[Start].as_long()
    hours = 9 + start_minutes // 60
    minutes = start_minutes % 60
    end_minutes = start_minutes + 60
    end_h = 9 + end_minutes // 60
    end_m = end_minutes % 60
    print(f"Monday {hours:02d}:{minutes:02d}-{end_h:02d}:{end_m:02d}")
else:
    print("No solution found")