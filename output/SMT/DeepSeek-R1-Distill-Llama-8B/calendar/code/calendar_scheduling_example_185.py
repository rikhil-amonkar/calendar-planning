import z3

def solve_scheduling():
    day = "Monday"
    # Convert busy intervals to minutes since 9:00
    kimberly_intervals = [
        (60, 90),          # 10:00-10:30
        (120, 150),        # 11:00-12:00
        (480, 510)         # 16:00-16:30
    ]
    marie_intervals = [
        (60, 90),          # 10:00-11:00
        (210, 330),        # 11:30-15:00
        (480, 510)         # 16:00-16:30
    ]
    diana_intervals = [
        (30, 60),          # 9:30-10:00
        (90, 210),         # 10:30-14:30
        (330, 1080)        # 15:30-17:00
    ]
    
    max_time = 1080        # 17:00
    earliest_start = 0     # 9:00
    latest_start = 60      # 10:00
    
    # Define the context
    ctx = z3.Context()
    
    # Variable for the start time in minutes (0 to 1080)
    s = z3.Int(ctx, "s")
    
    # Add constraints for each interval
    for a, b in kimberly_intervals:
        constraint = (s + 30) <= a | (b <= s)
        ctx.add(constraint)
    
    for a, b in marie_intervals:
        constraint = (s + 30) <= a | (b <= s)
        ctx.add(constraint)
    
    for a, b in diana_intervals:
        constraint = (s + 30) <= a | (b <= s)
        ctx.add(constraint)
    
    # Ensure Megan is available by starting no earlier than 10:00
    ctx.add(s >= latest_start)
    
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
        return (day, start_time, end_time)
    else:
        return None

solve_scheduling()