import z3

def solve_scheduling():
    day = "Monday"
    # Convert busy intervals to minutes since 9:00
    megan_intervals = [
        (0, 30),          # 9:00-9:30
        (60, 120),        # 10:00-11:00
        (120, 150)        # 12:00-12:30
    ]
    christine_intervals = [
        (0, 30),           # 9:00-9:30
        (90, 120),         # 11:30-12:00
        (180, 240),        # 13:00-14:00
        (270, 330)         # 15:30-16:30
    ]
    sara_intervals = [
        (90, 120),         # 11:30-12:00
        (270, 300)         # 14:30-15:00
    ]
    bruce_intervals = [
        (30, 60),          # 9:30-10:00
        (90, 180),         # 10:30-12:00
        (150, 210),        # 12:30-14:00
        (270, 300),        # 14:30-15:00
        (330, 360)         # 15:30-16:30
    ]
    kathryn_intervals = [
        (60, 330),          # 10:00-15:30
        (480, 510)         # 16:00-16:30
    ]
    billy_intervals = [
        (0, 30),           # 9:00-9:30
        (90, 120),         # 11:00-11:30
        (120, 210),        # 12:00-14:00
        (270, 300)         # 14:30-15:30
    ]
    
    max_time = 1080        # 17:00
    earliest_start = 0     # 9:00
    latest_start = 480     # 16:00
    
    # Define the context
    ctx = z3.Context()
    
    # Variable for the start time in minutes (0 to 1080)
    s = z3.Int(ctx, "s")
    
    # Add constraints for each interval
    for a, b in megan_intervals:
        constraint = (s + 30) <= a | (b <= s)
        ctx.add(constraint)
    
    for a, b in christine_intervals:
        constraint = (s + 30) <= a | (b <= s)
        ctx.add(constraint)
    
    for a, b in sara_intervals:
        constraint = (s + 30) <= a | (b <= s)
        ctx.add(constraint)
    
    for a, b in bruce_intervals:
        constraint = (s + 30) <= a | (b <= s)
        ctx.add(constraint)
    
    for a, b in kathryn_intervals:
        constraint = (s + 30) <= a | (b <= s)
        ctx.add(constraint)
    
    for a, b in billy_intervals:
        constraint = (s + 30) <= a | (b <= s)
        ctx.add(constraint)
    
    # Ensure the meeting starts after 9:00 and ends by 17:00
    ctx.add(s >= earliest_start)
    ctx.add(s + 30 <= max_time)
    
    # Ensure the meeting starts no later than 16:00
    ctx.add(s <= latest_start)
    
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