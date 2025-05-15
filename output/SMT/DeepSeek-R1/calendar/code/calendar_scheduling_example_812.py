from z3 import Solver, Int, Or, And, Optimize, sat

solver = Optimize()
Start = Int('Start')

# Define valid time ranges for each day (minutes since Monday 9:00)
solver.add(Or(
    And(0 <= Start, Start + 30 <= 480),    # Monday (0-480)
    And(480 <= Start, Start + 30 <= 960),  # Tuesday (480-960)
    And(960 <= Start, Start + 30 <= 1440), # Wednesday (960-1440)
    And(1440 <= Start, Start + 30 <= 1920) # Thursday (1440-1920)
))

# Add blocked time constraints
def add_block(start, end):
    solver.add(Or(Start + 30 <= start, Start >= end))

# Mary's blocked intervals
add_block(540, 570)    # Tuesday 10:00-10:30
add_block(870, 900)    # Tuesday 15:30-16:00
add_block(990, 1020)   # Wednesday 9:30-10:00
add_block(1320, 1350)  # Wednesday 15:00-15:30
add_block(1440, 1500)  # Thursday 9:00-10:00
add_block(1530, 1590)  # Thursday 10:30-11:30

# Alexis's blocked intervals
add_block(0, 60)       # Monday 9:00-10:00
add_block(90, 180)     # Monday 10:30-12:00
add_block(210, 450)    # Monday 12:30-16:30
add_block(480, 540)    # Tuesday 9:00-10:00
add_block(570, 630)    # Tuesday 10:30-11:30
add_block(660, 930)    # Tuesday 12:00-15:30
add_block(900, 960)    # Tuesday 16:00-17:00
add_block(960, 1080)   # Wednesday 9:00-11:00
add_block(1110, 1440)  # Wednesday 11:30-17:00
add_block(1500, 1620)  # Thursday 10:00-12:00
add_block(1740, 1770)  # Thursday 14:00-14:30
add_block(1830, 1860)  # Thursday 15:30-16:00
add_block(1890, 1920)  # Thursday 16:30-17:00

# Find earliest possible time
solver.minimize(Start)

if solver.check() == sat:
    model = solver.model()
    start_time = model[Start].as_long()
    
    # Determine day and convert to local time
    if start_time < 480:
        day, minutes = "Monday", start_time
    elif start_time < 960:
        day, minutes = "Tuesday", start_time - 480
    elif start_time < 1440:
        day, minutes = "Wednesday", start_time - 960
    else:
        day, minutes = "Thursday", start_time - 1440
    
    start_h = 9 + minutes // 60
    start_m = minutes % 60
    end_time = minutes + 30
    end_h = 9 + end_time // 60
    end_m = end_time % 60
    
    print(f"{day} {start_h:02d}:{start_m:02d}-{end_h:02d}:{end_m:02d}")
else:
    print("No solution found")