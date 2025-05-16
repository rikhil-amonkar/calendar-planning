import z3

def solve_scheduling():
    day = "Monday"
    # Convert busy intervals to minutes since 9:00
    anthony_intervals = [
        (30, 60),          # 9:30-10:00
        (120, 150),        # 12:00-13:00
        (480, 510)         # 16:00-16:30
    ]
    pamela_intervals = [
        (30, 60),           # 9:30-10:00
        (630, 1080)         # 16:30-17:00
    ]
    zachary_intervals = [
        (0, 90),            # 9:00-11:30
        (120, 150),        # 12:00-12:30
        (180, 210),        # 13:00-13:30
        (270, 330),        # 14:30-15:00
        (480, 1080)        # 16:00-17:00
    ]
    
    max_time = 1080        # 17:00
    latest_start = 450     # 14:30
    
    # Define the context
    ctx = z3.Context()
    
    # Variable for the start time in minutes (0 to 1080)
    s = z3.Int(ctx, "s")
    
    # Add constraints for each interval
    for a, b in anthony_intervals:
        constraint = (s >= a) | (b <= s)
        ctx.add(constraint)
    
    for a, b in pamela_intervals:
        constraint = (s >= a) | (b <= s)
        ctx.add(constraint)
    
    for a, b in zachary_intervals:
        constraint = (s >= a) | (b <= s)
        ctx.add(constraint)
    
    # Ensure the meeting starts no later than 14:30
    ctx.add(s <= latest_start)
    
    # Ensure the meeting starts after 9:00 and ends by 17:00
    ctx.add(s >= 0)
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
        return (day, start_time, end_time)
    else:
        return None

solve_scheduling()