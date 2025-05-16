import z3

def solve_scheduling():
    day = "Monday"
    # Convert busy intervals to minutes since 9:00
    gregory_intervals = [
        (0, 30),          # 9:00-9:30
        (120, 150),       # 11:30-12:00
    ]
    jonathan_intervals = [
        (0, 30),          # 9:00-9:30
        (60, 90),         # 12:00-12:30
        (180, 210),       # 13:00-13:30
        (300, 360),       # 15:00-16:00
        (330, 360),       # 16:30-17:00
    ]
    barbara_intervals = [
        (90, 120),        # 10:00-10:30
        (210, 240),       # 13:30-14:00
    ]
    jesse_intervals = [
        (90, 150),        # 10:00-11:00
        (150, 240),       # 12:30-14:30
    ]
    alan_intervals = [
        (30, 90),         # 9:30-11:00
        (120, 150),       # 11:30-12:30
        (180, 270),       # 13:00-15:30
        (300, 360),       # 16:00-17:00
    ]
    nicole_intervals = [
        (0, 90),          # 9:00-10:30
        (120, 150),       # 11:30-12:00
        (150, 180),       # 12:30-13:30
        (210, 360),       # 14:00-17:00
    ]
    catherine_intervals = [
        (0, 90),          # 9:00-10:30
        (60, 150),        # 12:00-13:30
        (300, 330),       # 15:00-15:30
        (360, 360),       # 16:00-16:30
    ]
    
    max_time = 1080        # 17:00
    earliest_start = 0     # 9:00
    latest_start = 480     # 16:00
    
    # Define the context
    ctx = z3.Context()
    
    # Variable for the start time in minutes (0 to 1080)
    s = z3.Int(ctx, "s")
    
    # Add constraints for each interval
    for a, b in gregory_intervals:
        constraint = (s + 30) <= a | (b <= s)
        ctx.add(constraint)
    
    for a, b in jonathan_intervals:
        constraint = (s + 30) <= a | (b <= s)
        ctx.add(constraint)
    
    for a, b in barbara_intervals:
        constraint = (s + 30) <= a | (b <= s)
        ctx.add(constraint)
    
    for a, b in jesse_intervals:
        constraint = (s + 30) <= a | (b <= s)
        ctx.add(constraint)
    
    for a, b in alan_intervals:
        constraint = (s + 30) <= a | (b <= s)
        ctx.add(constraint)
    
    for a, b in nicole_intervals:
        constraint = (s + 30) <= a | (b <= s)
        ctx.add(constraint)
    
    for a, b in catherine_intervals:
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