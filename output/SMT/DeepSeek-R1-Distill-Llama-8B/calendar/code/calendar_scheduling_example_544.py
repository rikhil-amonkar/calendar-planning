import z3

def solve_scheduling():
    day = "Monday"
    # Convert Albert's busy intervals to minutes since 9:00
    albert_intervals = [
        (0, 60),          # 9:00 to 10:00
        (90, 120),        # 10:30 to 12:00
        (540, 990)        # 15:00 to 16:30
    ]
    max_time = 1080       # 17:00 in minutes
    latest_start = 120    # 11:00 in minutes
    
    # Define the context
    ctx = z3.Context()
    
    # Variable for the start time in minutes (0 to 1080)
    s = z3.Int(ctx, "s")
    
    # Add constraints for each interval
    for a, b in albert_intervals:
        constraint = (s + 30) <= a | (b <= s)
        ctx.add(constraint)
    
    # Ensure the meeting starts no later than 11:00
    ctx.add(s <= latest_start)
    
    # Ensure the meeting ends by 17:00
    ctx.add(s + 30 <= max_time)
    
    # Ensure the meeting starts after 9:00
    ctx.add(s >= 0)
    
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