import z3

def solve_scheduling():
    day_options = ["Monday", "Tuesday", "Wednesday", "Thursday"]
    day = z3.Int("day", "0 to 3")
    
    # Convert busy intervals to minutes since 9:00
    betty_intervals = [
        # Monday
        (90, 120),        # 10:00-10:30
        (210, 240),       # 13:30-14:00
        (270, 300),       # 15:00-15:30
        (300, 360),       # 16:00-16:30
        # Tuesday
        (0, 30),          # 9:00-9:30
        (110, 120),       # 11:30-12:00
        (120, 150),       # 12:30-13:00
        (150, 180),       # 13:30-14:00
        (240, 360),       # 16:30-17:00
        # Wednesday
        (60, 90),         # 9:30-10:30
        (180, 210),       # 13:00-13:30
        (210, 240),       # 14:00-14:30
        # Thursday
        (60, 90),         # 9:30-10:00
        (110, 120),       # 11:30-12:00
        (180, 210),       # 12:30-13:00
        (210, 240),       # 14:00-14:30
        (270, 300),       # 15:00-15:30
        (300, 360)        # 16:30-17:00
    ]
    scott_intervals = [
        # Monday
        (30, 210),        # 9:30-15:00
        (270, 300),       # 15:30-16:00
        (300, 360),       # 16:30-17:00
        # Tuesday
        (0, 30),          # 9:00-9:30
        (60, 90),         # 10:00-11:00
        (90, 120),        # 11:30-12:00
        (120, 150),       # 12:30-13:30
        (180, 240),       # 14:00-15:00
        (240, 270),       # 16:00-16:30
        # Wednesday
        (30, 150),        # 9:30-12:30
        (180, 210),       # 13:00-13:30
        (210, 240),       # 14:00-14:30
        (270, 300),       # 15:00-15:30
        (300, 330),       # 16:00-16:30
        # Thursday
        (0, 30),          # 9:00-9:30
        (60, 90),         # 10:00-10:30
        (90, 120),        # 11:00-12:00
        (120, 150),       # 12:30-13:00
        (180, 210),       # 12:30-13:00
        (210, 240),       # 14:00-14:30
        (270, 300),       # 15:00-15:30
        (300, 360)        # 16:30-17:00
    ]
    
    max_time = 1080        # 17:00
    earliest_start = 0     # 9:00
    latest_start = 480     # 16:00
    
    # Define the context
    ctx = z3.Context()
    
    # Variable for the start time in minutes (0 to 1080)
    s = z3.Int(ctx, "s")
    
    # Add constraints for each interval
    for a, b in betty_intervals:
        constraint = (s + 30) <= a | (b <= s)
        ctx.add(constraint)
    
    for a, b in scott_intervals:
        constraint = (s + 30) <= a | (b <= s)
        ctx.add(constraint)
    
    # Ensure the meeting does not occur before 15:00 on Monday, Tuesday, or Thursday
    ctx.add((day == 0) | (day == 1) | (day == 3) & (s >= 300))
    
    # Ensure the meeting does not occur on Wednesday
    ctx.add(day != 2)
    
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