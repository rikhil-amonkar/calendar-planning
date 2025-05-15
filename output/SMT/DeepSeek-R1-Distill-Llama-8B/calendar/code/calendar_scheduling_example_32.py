import z3

def solve_scheduling():
    day = "Monday"
    # Convert busy intervals to minutes since 9:00
    emily_intervals = [
        (90, 120), # 10:00-10:30
        (150, 180), # 11:30-12:30
        (210, 240), # 14:00-15:00
        (300, 360)  # 16:00-16:30
    ]
    melissa_intervals = [
        (30, 60),   # 9:30-10:00
        (240, 270), # 14:30-15:00
    ]
    frank_intervals = [
        (60, 90),    # 10:00-10:30
        (90, 120),  # 11:00-11:30
        (150, 180), # 12:30-13:00
        (210, 240), # 13:30-14:00
        (270, 300), # 14:30-15:00
        (300, 360)  # 16:30-17:00
    ]
    
    max_time = 1080        # 17:00
    earliest_start = 0     # 9:00
    latest_start = 480     # 16:00
    
    # Define the context
    ctx = z3.Context()
    
    # Variable for the start time in minutes (0 to 1080)
    s = z3.Int(ctx, "s")
    
    # Add constraints for each interval
    for a, b in emily_intervals:
        constraint = (s + 30) <= a | (b <= s)
        ctx.add(constraint)
    
    for a, b in melissa_intervals:
        constraint = (s + 30) <= a | (b <= s)
        ctx.add(constraint)
    
    for a, b in frank_intervals:
        constraint = (s + 30) <= a | (b <= s)
        ctx.add(constraint)
    
    # Ensure the meeting starts no later than 9:30
    ctx.add(s <= 60)
    
    # Ensure the meeting starts after 9:00 and ends by 17:00
    ctx.add(s >= 0)
    ctx.add(s + 30 <= 1080)
    
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