import z3

def solve_scheduling():
    day_options = ["Monday", "Tuesday", "Wednesday"]
    day = z3.Int("day", "0 to 2")
    
    # Convert busy intervals to minutes since 9:00
    robert_intervals = [
        # Monday
        (90, 120),        # 11:00-11:30
        (210, 240),       # 14:00-14:30
        (300, 330),       # 15:30-16:00
        # Tuesday
        (90, 120),        # 10:30-11:00
        (270, 300),       # 15:00-15:30
        # Wednesday
        (60, 90),         # 10:00-11:00
        (150, 180),       # 11:30-12:00
        (180, 210),       # 12:30-13:00
        (210, 240),       # 13:30-14:00
        (300, 330),       # 15:00-15:30
        (360, 360)        # 16:00-16:30
    ]
    ralph_intervals = [
        # Monday
        (60, 210),        # 10:00-13:30
        (240, 270),       # 14:00-14:30
        (300, 360),       # 15:00-17:00
        # Tuesday
        (0, 30),          # 9:00-9:30
        (60, 90),         # 10:00-10:30
        (90, 150),        # 11:00-11:30
        (120, 180),       # 12:00-13:00
        (240, 270),       # 14:00-15:30
        (300, 360),       # 16:00-17:00
        # Wednesday
        (90, 120),        # 10:30-11:00
        (150, 180),       # 11:30-12:00
        (180, 210),       # 12:30-13:00
        (240, 300),       # 13:00-14:30
        (330, 360)        # 16:30-17:00
    ]
    
    max_time = 1080        # 17:00
    earliest_start = 0     # 9:00
    latest_start = 480     # 16:00
    
    # Define the context
    ctx = z3.Context()
    
    # Variable for the start time in minutes (0 to 1080)
    s = z3.Int(ctx, "s")
    
    # Add constraints for Robert's schedule
    for a, b in robert_intervals:
        constraint = (s + 30) <= a | (b <= s)
        ctx.add(constraint)
    
    # Add constraints for Ralph's schedule
    for a, b in ralph_intervals:
        constraint = (s + 30) <= a | (b <= s)
        ctx.add(constraint)
    
    # Ensure the meeting does not occur on Monday
    ctx.add(day != 0)
    
    # Ensure the meeting starts no later than 16:00
    ctx.add(s <= latest_start)
    
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