from z3 import *

# Define variables
day = Int('day')
start = Int('start')

# Blocked intervals for each participant by day (0: Monday, 1: Tuesday, 2: Wednesday)
blocked_martha = {
    0: [(960, 1020)],          # Monday
    1: [(900, 930)],           # Tuesday
    2: [(600, 660), (840, 870)]  # Wednesday
}

blocked_beverly = {
    0: [(540, 810), (840, 1020)],  # Monday
    1: [(540, 1020)],             # Tuesday
    2: [(570, 930), (990, 1020)]  # Wednesday
}

solver = Solver()

constraints = []
for day_num in [0, 1, 2]:
    martha_blocks = blocked_martha.get(day_num, [])
    beverly_blocks = blocked_beverly.get(day_num, [])
    
    day_constraints = [day == day_num]
    day_constraints.append(And(540 <= start, start <= 960))  # Meeting must be within work hours
    
    # Add non-overlapping constraints for Martha's blocked intervals
    for b_start, b_end in martha_blocks:
        day_constraints.append(Or(start + 60 <= b_start, start >= b_end))
    
    # Add non-overlapping constraints for Beverly's blocked intervals
    for b_start, b_end in beverly_blocks:
        day_constraints.append(Or(start + 60 <= b_start, start >= b_end))
    
    constraints.append(And(day_constraints))

solver.add(Or(constraints))

if solver.check() == sat:
    model = solver.model()
    day_val = model[day].as_long()
    start_val = model[start].as_long()
    
    # Map day number to day name
    days = ['Monday', 'Tuesday', 'Wednesday']
    day_name = days[day_val]
    
    # Convert start and end times to HH:MM format
    start_h = start_val // 60
    start_m = start_val % 60
    end_val = start_val + 60
    end_h = end_val // 60
    end_m = end_val % 60
    
    start_time = f"{start_h:02d}:{start_m:02d}"
    end_time = f"{end_h:02d}:{end_m:02d}"
    
    print(f"{day_name} {start_time}:{end_time}")
else:
    print("No solution")