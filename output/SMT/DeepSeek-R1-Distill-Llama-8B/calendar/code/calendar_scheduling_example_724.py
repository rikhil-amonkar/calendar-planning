import z3

def solve_scheduling():
    day_options = ["Monday", "Tuesday", "Wednesday"]
    day = z3.Int("day", "0 to 2")
    
    # Convert busy intervals to minutes since 9:00
    tyler_intervals = [
        # Tuesday
        (0, 30),          # 9:00-9:30
        (210, 240),        # 14:30-15:00
        # Wednesday
        (90, 120),         # 10:30-11:00
        (150, 180),        # 12:30-13:00
        (240, 270),        # 13:30-14:00
        (480, 540)         # 16:30-17:00
    ]
    
    ruth_intervals = [
        # Monday
        (0, 60),           # 9:00-10:00
        (90, 180),         # 10:30-12:00
        (210, 270),        # 12:30-14:30
        (300, 360),        # 15:00-16:00
        (480, 540),        # 16:30-17:00
        # Tuesday
        (0, 1080),          # 9:00-17:00
        # Wednesday
        (0, 1080)           # 9:00-17:00
    ]
    
    max_time = 1080        # 17:00
    earliest_start = 0     # 9:00
    latest_start = 480     # 16:00
    
    # Define the context
    ctx = z3.Context()
    
    # Variable for the start time in minutes (0 to 1080)
    s = z3.Int(ctx, "s")
    
    # Add constraints for Tyler's schedule
    for a, b in tyler_intervals:
        constraint = (s + 30) <= a | (b <= s)
        ctx.add(constraint)
    
    # Add constraints for Ruth's schedule
    for a, b in ruth_intervals:
        constraint = (s + 30) <= a | (b <= s)
        ctx.add(constraint)
    
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