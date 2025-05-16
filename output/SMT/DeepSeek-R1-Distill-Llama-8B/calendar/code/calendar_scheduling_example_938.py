import z3

def solve_scheduling():
    day_options = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]
    day = z3.Int("day", "0 to 4")
    
    # Convert busy intervals to minutes since 9:00
    eugene_intervals = [
        # Monday
        (90, 120),        # 11:00-12:00
        (210, 240),       # 13:30-14:00
        (270, 300),       # 14:30-15:00
        (300, 360),       # 16:00-16:30
        # Wednesday
        (0, 30),          # 9:00-9:30
        (90, 120),        # 11:00-11:30
        (120, 150),       # 12:00-12:30
        (210, 240),       # 13:30-14:00
        (270, 300),       # 14:30-15:00
        # Thursday
        (30, 60),         # 9:30-10:00
        (90, 150),        # 11:00-12:30
        # Friday
        (90, 120),        # 10:30-11:00
        (120, 150),       # 12:00-12:30
        (150, 180)        # 13:00-13:30
    ]
    eric_intervals = [
        # Monday
        (0, 360),          # 9:00-17:00
        # Tuesday
        (0, 360),          # 9:00-17:00
        # Wednesday
        (0, 30),           # 9:00-9:30
        (60, 90),          # 11:00-11:30
        (90, 150),         # 12:00-14:00
        (150, 180),        # 14:30-16:30
        # Thursday
        (0, 360),          # 9:00-17:00
        # Friday
        (0, 90),           # 9:00-11:00
        (90, 180),         # 11:30-17:00
    ]
    
    max_time = 1080        # 17:00
    earliest_start = 0     # 9:00
    latest_start = 480     # 16:00
    
    # Define the context
    ctx = z3.Context()
    
    # Variable for the start time in minutes (0 to 1080)
    s = z3.Int(ctx, "s")
    
    # Add constraints for each interval
    for a, b in eugene_intervals:
        constraint = (s + 30) <= a | (b <= s)
        ctx.add(constraint)
    
    for a, b in eric_intervals:
        constraint = (s + 30) <= a | (b <= s)
        ctx.add(constraint)
    
    # Ensure the meeting does not occur on Wednesday
    ctx.add(day != 2)
    
    # Ensure the meeting starts after 9:00 and ends by 17:00
    ctx.add(s >= earliest_start)
    ctx.add(s + 30 <= max_time)
    
    # Solve the problem
    result = ctx.solve()
    
    if result:
        # Convert s to time string
        start_min = result.model[s]
        start_h = start_min // 60
        start_m = start_min % 60
        start_time = f"{start_h:02d}:{start_m:02d}"
        end_min = start_min + 30
        end_h = end_min // 60
        end_m = end_min % 60
        end_time = f"{end_h:02d}:{end_m:02d}"
        day_str = day_options[result.model[day]]
        return (day_str, start_time, end_time)
    else:
        return None

solve_scheduling()