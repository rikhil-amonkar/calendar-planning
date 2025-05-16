import z3

def solve_scheduling():
    day = "Monday"
    # Convert busy intervals to minutes since 9:00
    adam_intervals = [
        (240, 300)  # 14:00-15:00
    ]
    john_intervals = [
        (180, 210),  # 13:00-13:30
        (240, 270),  # 14:00-14:30
        (300, 330),  # 15:30-16:00
        (330, 360)  # 16:30-17:00
    ]
    stephanie_intervals = [
        (30, 60),     # 9:30-10:00
        (90, 120),    # 10:30-11:00
        (150, 240),   # 11:30-16:00
        (270, 360)    # 16:30-17:00
    ]
    anna_intervals = [
        (30, 60),     # 9:30-10:00
        (60, 90),     # 12:00-12:30
        (180, 270),   # 13:00-15:30
        (270, 360)    # 16:30-17:00
    ]
    
    max_time = 1080        # 17:00
    earliest_start = 0     # 9:00
    latest_start = 480     # 14:30
    
    # Define the context
    ctx = z3.Context()
    
    # Variable for the start time in minutes (0 to 1080)
    s = z3.Int(ctx, "s")
    
    # Add constraints for each interval
    for a, b in adam_intervals:
        constraint = (s + 30) <= a | (b <= s)
        ctx.add(constraint)
    
    for a, b in john_intervals:
        constraint = (s + 30) <= a | (b <= s)
        ctx.add(constraint)
    
    for a, b in stephanie_intervals:
        constraint = (s + 30) <= a | (b <= s)
        ctx.add(constraint)
    
    for a, b in anna_intervals:
        constraint = (s + 30) <= a | (b <= s)
        ctx.add(constraint)
    
    # Ensure the meeting starts no later than 14:30
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