import z3

def solve_scheduling():
    day = "Monday"
    # Convert busy intervals to minutes since 9:00
    shirley_intervals = [
        (150, 180), # 10:30-11:00
        (180, 210)  # 12:00-12:30
    ]
    jacob_intervals = [
        (0, 30),    # 9:00-9:30
        (60, 90),   # 10:00-10:30
        (90, 120),  # 11:00-11:30
        (150, 180), # 12:30-13:30
        (240, 270)  # 14:30-15:00
    ]
    stephen_intervals = [
        (150, 180), # 11:30-12:00
        (180, 210)  # 12:30-13:00
    ]
    margaret_intervals = [
        (0, 30),    # 9:00-9:30
        (90, 150),  # 10:30-12:30
        (180, 210), # 13:00-13:30
        (270, 300), # 15:00-15:30
        (300, 360)  # 16:30-17:00
    ]
    mason_intervals = [
        (0, 60),    # 9:00-10:00
        (90, 120),  # 10:30-11:00
        (150, 180), # 11:30-12:30
        (180, 210), # 13:00-13:30
        (240, 270), # 14:00-14:30
        (300, 360)  # 16:30-17:00
    ]
    
    max_time = 1080        # 17:00
    earliest_start = 0     # 9:00
    latest_start = 480     # 14:30
    
    # Define the context
    ctx = z3.Context()
    
    # Variable for the start time in minutes (0 to 1080)
    s = z3.Int(ctx, "s")
    
    # Add constraints for each interval
    for a, b in shirley_intervals:
        constraint = (s + 30) <= a | (b <= s)
        ctx.add(constraint)
    
    for a, b in jacob_intervals:
        constraint = (s + 30) <= a | (b <= s)
        ctx.add(constraint)
    
    for a, b in stephen_intervals:
        constraint = (s + 30) <= a | (b <= s)
        ctx.add(constraint)
    
    for a, b in margaret_intervals:
        constraint = (s + 30) <= a | (b <= s)
        ctx.add(constraint)
    
    for a, b in mason_intervals:
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