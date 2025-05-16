import z3

def solve_scheduling():
    day = "Monday"
    # Convert busy intervals to minutes since 9:00
    jose_intervals = [
        (90, 120), # 11:00-11:30
        (150, 180), # 12:30-13:00
    ]
    keith_intervals = [
        (210, 240), # 14:00-14:30
        (270, 300), # 15:00-15:30
    ]
    logan_intervals = [
        (0, 60),    # 9:00-10:00
        (120, 150), # 12:00-12:30
        (240, 270), # 15:00-15:30
    ]
    megan_intervals = [
        (0, 90),    # 9:00-10:30
        (90, 120),  # 11:00-12:00
        (180, 210), # 13:00-13:30
        (270, 300), # 14:30-16:30
    ]
    gary_intervals = [
        (0, 30),    # 9:00-9:30
        (60, 90),   # 10:00-10:30
        (90, 150),  # 11:30-13:00
        (180, 210), # 13:00-14:00
        (270, 300), # 14:30-16:30
    ]
    bobby_intervals = [
        (90, 120),  # 11:00-11:30
        (120, 150), # 12:00-12:30
        (180, 240), # 13:00-16:00
    ]
    
    max_time = 1080        # 17:00
    earliest_start = 0     # 9:00
    latest_start = 480     # 16:00
    
    # Define the context
    ctx = z3.Context()
    
    # Variable for the start time in minutes (0 to 1080)
    s = z3.Int(ctx, "s")
    
    # Add constraints for each interval
    for a, b in jose_intervals:
        constraint = (s + 30) <= a | (b <= s)
        ctx.add(constraint)
    
    for a, b in keith_intervals:
        constraint = (s + 30) <= a | (b <= s)
        ctx.add(constraint)
    
    for a, b in logan_intervals:
        constraint = (s + 30) <= a | (b <= s)
        ctx.add(constraint)
    
    for a, b in megan_intervals:
        constraint = (s + 30) <= a | (b <= s)
        ctx.add(constraint)
    
    for a, b in gary_intervals:
        constraint = (s + 30) <= a | (b <= s)
        ctx.add(constraint)
    
    for a, b in bobby_intervals:
        constraint = (s + 30) <= a | (b <= s)
        ctx.add(constraint)
    
    # Ensure the meeting starts no later than 15:30
    ctx.add(s <= 480)
    
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