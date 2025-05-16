from z3 import Solver, Int, Or, And, Optimize, If, sat

solver = Optimize()
Start = Int('Start')

# Define valid time ranges for Monday and Tuesday (minutes since Monday 9:00)
solver.add(Or(
    And(0 <= Start, Start + 30 <= 480),    # Monday (0-480)
    And(480 <= Start, Start + 30 <= 960)   # Tuesday (480-960)
))

# Penalize Monday meetings before 14:30 (330 minutes from Monday start)
monday_penalty = If(And(Start < 330, Start >= 0), 1, 0)
solver.minimize(monday_penalty)
solver.minimize(Start)  # Then find earliest time

def add_block(start, end):
    solver.add(Or(Start + 30 <= start, Start >= end))

# Ryan's blocked intervals
# Monday
add_block(30, 60)     # 9:30-10:00
add_block(120, 180)   # 11:00-12:00
add_block(240, 270)   # 13:00-13:30
add_block(390, 420)   # 15:30-16:00
# Tuesday
add_block(630, 660)   # 11:30-12:30
add_block(870, 900)   # 15:30-16:00

# Adam's blocked intervals
# Monday
add_block(0, 90)      # 9:00-10:30
add_block(120, 270)   # 11:00-13:30
add_block(300, 420)   # 14:00-16:00
add_block(450, 480)   # 16:30-17:00
# Tuesday
add_block(480, 540)   # 9:00-10:00
add_block(570, 870)   # 10:30-15:30
add_block(900, 960)   # 16:00-17:00

if solver.check() == sat:
    model = solver.model()
    start_time = model[Start].as_long()
    
    # Determine day and convert to local time
    if start_time < 480:
        day, minutes = "Monday", start_time
    else:
        day, minutes = "Tuesday", start_time - 480
    
    start_h = 9 + minutes // 60
    start_m = minutes % 60
    end_time = minutes + 30
    end_h = 9 + end_time // 60
    end_m = end_time % 60
    
    print(f"{day} {start_h:02d}:{start_m:02d}-{end_h:02d}:{end_m:02d}")
else:
    print("No solution found")