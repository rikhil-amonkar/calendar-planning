from z3 import Solver, Int, Or, And, Optimize, sat

solver = Optimize()
Start = Int('Start')

# Define valid time ranges for all days (minutes since Monday 9:00)
solver.add(Or(
    And(0 <= Start, Start + 60 <= 480),    # Monday (0-480 mins)
    And(480 <= Start, Start + 60 <= 960),  # Tuesday (480-960 mins)
    And(960 <= Start, Start + 60 <= 1440)  # Wednesday (960-1440 mins)
))

# Find earliest possible time
solver.minimize(Start)

def add_block(start, end):
    solver.add(Or(Start + 60 <= start, Start >= end))

# Roy's blocked intervals
# Monday
add_block(60, 150)     # 10:00-11:30
add_block(180, 240)    # 12:00-13:00
add_block(300, 330)    # 14:00-14:30
add_block(360, 480)    # 15:00-17:00

# Tuesday
add_block(570, 630)    # 10:30-11:30
add_block(660, 810)    # 12:00-14:30
add_block(840, 870)    # 15:00-15:30
add_block(900, 960)    # 16:00-17:00

# Wednesday
add_block(990, 1110)   # 9:30-11:30
add_block(1170, 1260)  # 12:30-14:00
add_block(1290, 1350)  # 14:30-15:30
add_block(1410, 1440)  # 16:30-17:00

# Patrick has no blocked intervals

if solver.check() == sat:
    model = solver.model()
    start_time = model[Start].as_long()
    
    # Determine day and convert to local time
    if start_time < 480:
        day, minutes = "Monday", start_time
    elif start_time < 960:
        day, minutes = "Tuesday", start_time - 480
    else:
        day, minutes = "Wednesday", start_time - 960
    
    start_h = 9 + minutes // 60
    start_m = minutes % 60
    end_time = minutes + 60
    end_h = 9 + end_time // 60
    end_m = end_time % 60
    
    print(f"{day} {start_h:02d}:{start_m:02d}-{end_h:02d}:{end_m:02d}")
else:
    print("No solution found")