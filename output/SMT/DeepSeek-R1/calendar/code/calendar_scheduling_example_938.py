from z3 import Solver, Int, Or, And, Optimize, If, sat

solver = Optimize()
Start = Int('Start')

# Define valid time ranges for each day (minutes since Monday 9:00)
solver.add(Or(
    And(0 <= Start, Start + 30 <= 480),        # Monday (0-480)
    And(480 <= Start, Start + 30 <= 960),      # Tuesday (480-960)
    And(960 <= Start, Start + 30 <= 1440),     # Wednesday (960-1440)
    And(1440 <= Start, Start + 30 <= 1920),    # Thursday (1440-1920)
    And(1920 <= Start, Start + 30 <= 2400)     # Friday (1920-2400)
))

# Penalize Wednesday meetings to prioritize other days
wednesday_penalty = If(And(960 <= Start, Start < 1440), 1, 0)
solver.minimize(wednesday_penalty)
solver.minimize(Start)  # Then find earliest time

# Add blocked time constraints
def add_block(start, end):
    solver.add(Or(Start + 30 <= start, Start >= end))

# Eugene's blocked intervals (global minutes)
add_block(120, 180)    # Monday 11:00-12:00
add_block(270, 300)    # Monday 13:30-14:00
add_block(330, 360)    # Monday 14:30-15:00
add_block(420, 450)    # Monday 16:00-16:30
add_block(960, 990)    # Wednesday 9:00-9:30
add_block(1080, 1110)  # Wednesday 11:00-11:30
add_block(1140, 1170)  # Wednesday 12:00-12:30
add_block(1230, 1380)  # Wednesday 13:30-15:00
add_block(1470, 1500)  # Thursday 9:30-10:00
add_block(1500, 1650)  # Thursday 11:00-12:30
add_block(2010, 2040)  # Friday 10:30-11:00
add_block(2040, 2070)  # Friday 12:00-12:30
add_block(2100, 2130)  # Friday 13:00-13:30

# Eric's blocked intervals (global minutes)
add_block(0, 480)      # Monday all day
add_block(480, 960)    # Tuesday all day
add_block(960, 1110)   # Wednesday 9:00-11:30
add_block(1140, 1320)  # Wednesday 12:00-14:00
add_block(1350, 1590)  # Wednesday 14:30-16:30
add_block(1440, 1920)  # Thursday all day
add_block(1920, 2040)  # Friday 9:00-11:00
add_block(2070, 2400)  # Friday 11:30-17:00

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
    elif start_time < 1920:
        day, minutes = "Thursday", start_time - 1440
    else:
        day, minutes = "Friday", start_time - 1920
    
    start_h = 9 + minutes // 60
    start_m = minutes % 60
    end_time = minutes + 30
    end_h = 9 + end_time // 60
    end_m = end_time % 60
    
    print(f"{day} {start_h:02d}:{start_m:02d}-{end_h:02d}:{end_m:02d}")
else:
    print("No solution found")