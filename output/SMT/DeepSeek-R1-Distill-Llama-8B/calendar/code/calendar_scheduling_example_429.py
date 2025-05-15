import z3

def solve_scheduling():
    day = "Monday"
    # Convert busy intervals to minutes since 9:00
    judy_intervals = [
        (210, 240), # 13:00-13:30
        (300, 330)  # 16:00-16:30
    ]
    olivia_intervals = [
        (90, 120), # 10:00-10:30
        (120, 150), # 12:00-13:00
        (180, 210)  # 14:00-14:30
    ]
    jacqueline_intervals = [
        (90, 120), # 10:00-10:30
        (270, 300)  # 15:00-15:30
    ]
    laura_intervals = [
        (0, 60),    # 9:00-10:00
        (90, 150),  # 10:30-12:00
        (180, 210), # 13:00-13:30
        (240, 270), # 14:30-15:00
        (270, 360)  # 15:30-17:00
    ]
    tyler_intervals = [
        (0, 60),    # 9:00-10:00
        (90, 120),  # 11:00-11:30
        (150, 180), # 12:30-13:00
        (210, 240), # 14:00-14:30
        (270, 300), # 15:30-16:00
        (300, 360)  # 16:30-17:00
    ]
    lisa_intervals = [
        (30, 90),   # 9:30-10:30
        (90, 120),  # 11:00-11:30
        (120, 150), # 12:00-12:30
        (180, 210), # 13:00-13:30
        (240, 270), # 14:00-14:30
        (300, 360)  # 16:00-17:00
    ]
    
    max_time = 1080        # 17:00
    earliest_start = 0     # 9:00
    latest_start = 480     # 16:00
    
    # Define the context
    ctx = z3.Context()
    
    # Variable for the start time in minutes (0 to 1080)
    s = z3.Int(ctx, "s")
    
    # Add constraints for each interval
    for a, b in judy_intervals:
        constraint = (s + 30) <= a | (b <= s)
        ctx.add(constraint)
    
    for a, b in olivia_intervals:
        constraint = (s + 30) <= a | (b <= s)
        ctx.add(constraint)
    
    for a, b in jacqueline_intervals:
        constraint = (s + 30) <= a | (b <= s)
        ctx.add(constraint)
    
    for a, b in laura_intervals:
        constraint = (s + 30) <= a | (b <= s)
        ctx.add(constraint)
    
    for a, b in tyler_intervals:
        constraint = (s + 30) <= a | (b <= s)
        ctx.add(constraint)
    
    for a, b in lisa_intervals:
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