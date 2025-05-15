import z3

solver = z3.Optimize()
S = z3.Int('S')

# Convert time to minutes since Monday 9:00
solver.add(z3.Or(
    z3.And(S >= 0, S + 30 <= 480),    # Monday
    z3.And(S >= 480, S + 30 <= 960),  # Tuesday
    z3.And(S >= 960, S + 30 <= 1440)  # Wednesday
))

# Cheryl cannot meet on Wednesday (block days 960-1440)
solver.add(S < 960)

# Cheryl's blocked intervals (minutes since Monday 9:00)
cheryl_blocks = [
    (0, 30), (150, 240), (390, 420),   # Monday
    (840, 870),                        # Tuesday
]

# Kyle's blocked intervals (minutes since Monday 9:00)
kyle_blocks = [
    (0, 480),                          # Monday
    (510, 960),                        # Tuesday
    (960, 990), (1020, 1170), (1230, 1290), (1320, 1440)  # Wednesday
]

# Add availability constraints for both participants
for start, end in cheryl_blocks + kyle_blocks:
    solver.add(z3.Or(S + 30 <= start, S >= end))

# Find earliest possible time
solver.minimize(S)

if solver.check() == z3.sat:
    model = solver.model()
    start_total = model[S].as_long()
    
    if start_total < 480:
        day = "Monday"
        start_on_day = start_total
    elif start_total < 960:
        day = "Tuesday"
        start_on_day = start_total - 480
    else:
        day = "Wednesday"
        start_on_day = start_total - 960
    
    start_h = 9 + start_on_day // 60
    start_m = start_on_day % 60
    end_total = start_total + 30
    end_on_day = end_total - (480 if day == "Tuesday" else 960 if day == "Wednesday" else 0)
    end_h = 9 + end_on_day // 60
    end_m = end_on_day % 60
    
    print(f"{day}\n{start_h}:{start_m:02d}\n{end_h}:{end_m:02d}")
else:
    print("No solution found")