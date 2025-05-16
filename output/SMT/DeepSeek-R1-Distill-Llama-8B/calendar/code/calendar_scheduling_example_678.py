import z3

def solve_scheduling():
    day_options = ["Monday", "Tuesday"]
    day = z3.Int("day", "0 to 1")
    
    # Convert busy intervals to minutes since 9:00
    russell_intervals = [
        # Monday
        (150, 180),       # 10:30-11:00
        # Tuesday
        (210, 240),       # 13:00-13:30
    ]
    alexander_intervals = [
        # Monday
        (0, 90),          # 9:00-11:30
        (90, 180),        # 12:00-14:30
        (210, 360),       # 15:00-17:00
        # Tuesday
        (0, 60),          # 9:00-10:00
        (120, 150),       # 13:00-14:00
        (180, 210),       # 15:00-15:30
        (240, 270),       # 16:00-16:30
    ]
    
    max_time = 1080        # 17:00
    earliest_start = 0     # 9:00
    latest_start = 480     # 16:00
    
    # Define the context
    ctx = z3.Context()
    
    # Variable for the start time in minutes (0 to 1080)
    s = z3.Int(ctx, "s")
    
    # Add constraints for each interval
    for a, b in russell_intervals:
        constraint = (s + 60) <= a | (b <= s)
        ctx.add(constraint)
    
    for a, b in alexander_intervals:
        constraint = (s + 60) <= a | (b <= s)
        ctx.add(constraint)
    
    # Ensure the meeting does not occur before 13:30 on Tuesday
    ctx.add((day == 1) & (s >= 210))
    
    # Ensure the meeting starts after 9:00 and ends by 17:00
    ctx.add(s >= earliest_start)
    ctx.add(s + 60 <= max_time)
    
    # Solve the problem
    result = ctx.solve()
    
    if result:
        # Convert s to time string
        start_min = result.model[s]
        start_h = start_min // 60
        start_m = start_min % 60
        start_time = f"{start_h:02d}:{start_m:02d}"
        end_min = start_min + 60
        end_h = end_min // 60
        end_m = end_min % 60
        end_time = f"{end_h:02d}:{end_m:02d}"
        day_str = day_options[result.model[day]]
        return (day_str, start_time, end_time)
    else:
        return None

solve_scheduling()