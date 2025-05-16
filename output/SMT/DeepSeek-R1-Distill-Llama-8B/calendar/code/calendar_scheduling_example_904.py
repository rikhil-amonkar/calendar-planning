import z3

def solve_scheduling():
    day_options = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]
    day = z3.Int("day", "0 to 4")
    
    # Convert busy intervals to minutes since 9:00
    daniel_intervals = [
        # Monday
        (30, 60),   # 9:30-10:30
        (120, 150), # 12:00-12:30
        (180, 210), # 13:00-14:00
        (240, 270), # 14:30-15:00
        (300, 330), # 15:30-16:00
        # Tuesday
        (90, 120),  # 11:00-12:00
        (150, 180), # 13:00-13:30
        (210, 240), # 15:30-16:00
        (240, 270), # 16:30-17:00
        # Wednesday
        (0, 60),    # 9:00-10:00
        (60, 120),  # 11:00-12:00
        (150, 180), # 12:30-13:00
        (240, 270), # 14:30-15:00
        # Thursday
        (90, 120),  # 11:00-12:00
        (150, 180), # 12:30-13:00
        (210, 240), # 14:30-15:00
        # Friday
        (30, 60),   # 9:30-10:30
        (90, 120),  # 11:00-12:00
        (150, 180), # 12:30-13:00
        (210, 240), # 14:30-15:00
        (270, 300)  # 16:30-17:00
    ]
    bradley_intervals = [
        # Monday
        (30, 90),    # 9:30-11:00
        (90, 120),   # 11:30-12:00
        (150, 180),  # 12:30-13:00
        (210, 240),  # 14:00-15:00
        # Tuesday
        (90, 120),   # 10:30-11:00
        (120, 150),  # 12:00-13:00
        (150, 180),  # 13:30-14:00
        (210, 240),  # 15:30-16:00
        (240, 270),  # 16:30-17:00
        # Wednesday
        (0, 60),     # 9:00-10:00
        (60, 120),   # 11:00-12:00
        (120, 150),  # 12:30-13:00
        (180, 210),  # 13:00-14:00
        (240, 270),  # 14:30-15:00
        (270, 300),  # 15:30-16:00
        # Thursday
        (0, 90),     # 9:00-10:30
        (90, 120),   # 10:30-11:00
        (120, 150),  # 12:00-12:30
        (180, 210),  # 13:00-14:00
        (240, 270),  # 14:30-15:00
        # Friday
        (30, 60),    # 9:30-10:30
        (90, 120),   # 11:00-12:00
        (150, 180),  # 12:30-13:00
        (210, 240),  # 14:30-15:00
        (270, 300)   # 16:30-17:00
    ]
    
    max_time = 1080        # 17:00
    earliest_start = 0     # 9:00
    latest_start = 480     # 16:00
    
    # Define the context
    ctx = z3.Context()
    
    # Variable for the start time in minutes (0 to 1080)
    s = z3.Int(ctx, "s")
    
    # Add constraints for each interval
    for a, b in daniel_intervals:
        constraint = (s + 30) <= a | (b <= s)
        ctx.add(constraint)
    
    for a, b in bradley_intervals:
        constraint = (s + 30) <= a | (b <= s)
        ctx.add(constraint)
    
    # Ensure the meeting does not occur on Wednesday or Thursday for Daniel
    ctx.add((day == 2) | (day == 3))
    
    # Ensure the meeting does not occur on Monday or Tuesday before 12:00 for Bradley
    ctx.add((day == 0) | (day == 1) & (s >= 120))
    
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
        day_str = day_options[result.model[day]]
        return (day_str, start_time, end_time)
    else:
        return None

solve_scheduling()