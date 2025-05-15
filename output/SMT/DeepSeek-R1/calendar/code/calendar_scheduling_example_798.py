import z3

solver = z3.Optimize()
S = z3.Int('S')

# Work hours: Monday (0-480), Tuesday (480-960), Wednesday (960-1440)
solver.add(z3.Or(
    z3.And(S >= 0, S + 30 <= 480),   # Monday
    z3.And(S >= 480, S + 30 <= 960), # Tuesday
    z3.And(S >= 960, S + 30 <= 1440) # Wednesday
))

# Nancy's blocked intervals (minutes since Monday 9:00)
nancy_blocks = [
    # Monday
    (60, 90), (150, 210), (270, 300), (330, 390), (420, 480),
    # Tuesday
    (510, 570), (600, 630), (660, 690), (720, 750), (870, 900),
    # Wednesday
    (1020, 1110), (1230, 1380)
]

# Jose's blocked intervals (minutes since Monday 9:00)
jose_blocks = [
    # Monday
    (0, 480),
    # Tuesday
    (480, 960),
    # Wednesday
    (960, 990), (1020, 1170), (1230, 1290), (1320, 1440)
]

# Add constraints for both participants' availability
for start, end in nancy_blocks + jose_blocks:
    solver.add(z3.Or(S + 30 <= start, S >= end))

# Minimize start time to find earliest possible meeting
solver.minimize(S)

if solver.check() == z3.sat:
    model = solver.model()
    start_total = model[S].as_long()
    
    # Determine day and adjust time within the day
    if start_total < 480:
        day = "Monday"
        start_on_day = start_total
    elif start_total < 960:
        day = "Tuesday"
        start_on_day = start_total - 480
    else:
        day = "Wednesday"
        start_on_day = start_total - 960
    
    # Calculate start and end times
    start_h = 9 + start_on_day // 60
    start_m = start_on_day % 60
    end_total = start_total + 30
    end_on_day = end_total - (480 if day == "Tuesday" else 960 if day == "Wednesday" else 0)
    end_h = 9 + end_on_day // 60
    end_m = end_on_day % 60
    
    print(f"{day}\n{start_h}:{start_m:02d}\n{end_h}:{end_m:02d}")
else:
    print("No solution found")