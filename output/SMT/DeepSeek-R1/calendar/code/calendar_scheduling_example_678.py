from z3 import Solver, Int, Or, And, Optimize, If, sat

solver = Optimize()
Start = Int('Start')

# Define valid time ranges for Monday and Tuesday (minutes since Monday 9:00)
solver.add(Or(
    And(0 <= Start, Start + 60 <= 480),   # Monday (0-480 minutes)
    And(480 <= Start, Start + 60 <= 960)  # Tuesday (480-960 minutes)
))

# Add penalty for Tuesday meetings before 13:30 (750 minutes from Monday 9:00)
tuesday_penalty = If(And(480 <= Start, Start < 750), 1, 0)
solver.minimize(tuesday_penalty)
solver.minimize(Start)  # Then find earliest time

# Function to add blocked time ranges
def add_block(start, end):
    solver.add(Or(Start + 60 <= start, Start >= end))

# Russell's blocked intervals
add_block(90, 120)    # Monday 10:30-11:00 (90-120 mins)
add_block(720, 750)   # Tuesday 13:00-13:30 (720-750 mins)

# Alexander's blocked intervals
# Monday
add_block(0, 150)     # 9:00-11:30
add_block(180, 330)   # 12:00-14:30
add_block(360, 480)   # 15:00-17:00
# Tuesday
add_block(480, 540)   # 9:00-10:00
add_block(720, 780)   # 13:00-14:00
add_block(840, 870)   # 15:00-15:30
add_block(900, 930)   # 16:00-16:30

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
    end_time = minutes + 60
    end_h = 9 + end_time // 60
    end_m = end_time % 60
    
    print(f"{day} {start_h:02d}:{start_m:02d}-{end_h:02d}:{end_m:02d}")
else:
    print("No solution found")