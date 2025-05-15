import z3

def solve_scheduling():
    day = "Monday"
    # Convert busy intervals to minutes since 9:00
    steven_intervals = []
    roy_intervals = []
    cynthia_intervals = [
        (150, 180), # 12:30-13:30
        (210, 240), # 13:00-14:00
        (270, 300), # 14:30-15:00
        (300, 360)  # 16:30-17:00
    ]
    lauren_intervals = [
        (90, 120), # 10:30-11:00
        (150, 180), # 12:30-13:30
        (210, 240), # 13:00-14:00
        (270, 300), # 14:30-15:00
        (300, 360)  # 16:30-17:00
    ]
    robert_intervals = [
        (150, 180), # 12:30-13:30
        (210, 240), # 13:00-14:00
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
    for a, b in cynthia_intervals:
        constraint = (s + 30) <= a | (b <= s)
        ctx.add(constraint)
    
    for a, b in lauren_intervals:
        constraint = (s + 30) <= a | (b <= s)
        ctx.add(constraint)
    
    for a, b in robert_intervals:
        constraint = (s + 30) <= a | (b <= s)
        ctx.add(constraint)
    
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