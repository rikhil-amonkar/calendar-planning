import z3

def solve_scheduling():
    day = "Monday"
    # Convert busy intervals to minutes since 9:00
    cheryl_intervals = [
        (0, 30),          # 9:00-9:30
        (60, 150),        # 10:00-11:30
        (150, 180),       # 12:30-13:30
        (240, 360)        # 14:00-17:00
    ]
    virginia_intervals = [
        (30, 150),        # 9:30-11:30
        (60, 90),         # 12:00-12:30
        (120, 150),       # 13:00-13:30
        (270, 330),       # 14:30-15:30
        (480, 540)        # 16:00-17:00
    ]
    angela_intervals = [
        (30, 60),          # 9:30-10:00
        (90, 150),         # 10:30-11:30
        (60, 90),          # 12:00-12:30
        (120, 150),        # 13:00-13:30
        (240, 330)         # 14:00-16:30
    ]
    
    max_time = 1080        # 17:00
    earliest_start = 0     # 9:00
    latest_start = 480     # 12:30
    
    # Define the context
    ctx = z3.Context()
    
    # Variable for the start time in minutes (0 to 1080)
    s = z3.Int(ctx, "s")
    
    # Add constraints for each interval
    for a, b in cheryl_intervals:
        constraint = (s + 30) <= a | (b <= s)
        ctx.add(constraint)
    
    for a, b in virginia_intervals:
        constraint = (s + 30) <= a | (b <= s)
        ctx.add(constraint)
    
    for a, b in angela_intervals:
        constraint = (s + 30) <= a | (b <= s)
        ctx.add(constraint)
    
    # Ensure the meeting starts no later than 12:30
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
        return (day, start_time, end_time)
    else:
        return None

solve_scheduling()