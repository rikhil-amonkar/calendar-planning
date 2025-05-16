import z3

def solve_scheduling():
    day = "Monday"
    # Convert busy intervals to minutes since 9:00
    stephanie_intervals = [
        (90, 105),        # 11:00-11:30
        (210, 225)        # 14:30-15:00
    ]
    joe_intervals = [
        (0, 30),          # 9:00-9:30
        (60, 180),        # 10:00-12:00
        (150, 180),       # 12:30-13:00
        (240, 360)        # 14:00-17:00
    ]
    diana_intervals = [
        (0, 90),           # 9:00-10:30
        (150, 180),       # 11:30-12:00
        (180, 240),       # 13:00-14:00
        (270, 330),       # 14:30-15:30
        (480, 540)        # 16:00-17:00
    ]
    deborah_intervals = [
        (0, 60),           # 9:00-10:00
        (90, 180),        # 10:30-12:00
        (150, 180),       # 12:30-13:00
        (210, 240),       # 13:30-14:00
        (270, 330),       # 14:30-15:30
        (480, 510)        # 16:00-16:30
    ]
    
    max_time = 1080        # 17:00
    earliest_start = 0     # 9:00
    
    # Define the context
    ctx = z3.Context()
    
    # Variable for the start time in minutes (0 to 1080)
    s = z3.Int(ctx, "s")
    
    # Add constraints for each interval
    for a, b in stephanie_intervals:
        constraint = (s >= a) | (b <= s)
        ctx.add(constraint)
    
    for a, b in joe_intervals:
        constraint = (s >= a) | (b <= s)
        ctx.add(constraint)
    
    for a, b in diana_intervals:
        constraint = (s >= a) | (b <= s)
        ctx.add(constraint)
    
    for a, b in deborah_intervals:
        constraint = (s >= a) | (b <= s)
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