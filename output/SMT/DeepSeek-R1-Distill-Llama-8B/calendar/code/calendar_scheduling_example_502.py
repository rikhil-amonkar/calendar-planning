import z3

def solve_scheduling():
    day = "Monday"
    # Convert busy intervals to minutes since 9:00
    jack_intervals = [
        (30, 90),          # 9:30-10:30
        (60, 75),          # 11:00-11:30
        (150, 180),        # 12:30-13:00
        (210, 240),        # 14:00-14:30
        (480, 510)         # 16:00-16:30
    ]
    charlotte_intervals = [
        (30, 60),           # 9:30-10:00
        (90, 180),          # 10:30-12:00
        (150, 210),         # 12:30-13:30
        (210, 480)          # 14:00-16:00
    ]
    max_time = 1080        # 17:00
    latest_start = 150     # 12:30
    
    # Define the context
    ctx = z3.Context()
    
    # Variable for the start time in minutes (0 to 1080)
    s = z3.Int(ctx, "s")
    
    # Add constraints for each interval
    for a, b in jack_intervals:
        constraint = (s + 30) <= a | (b <= s)
        ctx.add(constraint)
    
    for a, b in charlotte_intervals:
        constraint = (s + 30) <= a | (b <= s)
        ctx.add(constraint)
    
    # Add constraint for Jack's preference: start no later than 12:30
    ctx.add(s <= latest_start)
    
    # Ensure the meeting starts after 9:00 and ends by 17:00
    ctx.add(s >= 0)
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