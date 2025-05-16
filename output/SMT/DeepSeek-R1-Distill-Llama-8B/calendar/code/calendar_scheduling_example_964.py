import z3

def solve_scheduling():
    day_options = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]
    day = z3.Int("day", "0 to 4")
    
    # Convert busy intervals to minutes since 9:00
    betty_intervals = [
        # Monday
        (60, 90),          # 10:00-10:30
        (150, 180),        # 11:30-12:30
        (480, 540),        # 16:00-16:30
        # Tuesday
        (30, 60),          # 9:30-10:00
        (90, 120),         # 10:30-11:00
        (120, 150),        # 12:00-12:30
        (210, 300),        # 13:30-15:00
        (330, 360),        # 16:30-17:00
        # Wednesday
        (240, 270),        # 13:30-14:00
        (270, 300),        # 14:30-15:00
        # Thursday
        # No meetings
        # Friday
        (0, 60),           # 9:00-10:00
        (150, 180),        # 11:30-12:00
        (180, 210),        # 12:30-13:00
        (270, 300)         # 14:30-15:00
    ]
    megan_intervals = [
        # Monday
        (0, 1080),          # 9:00-17:00
        # Tuesday
        (30, 90),           # 9:30-10:00
        (90, 180),          # 10:30-12:00
        (180, 240),         # 12:00-14:00
        (270, 330),         # 15:00-15:30
        (330, 360),         # 16:00-16:30
        # Wednesday
        (60, 120),          # 9:30-11:30
        (120, 150),         # 12:00-12:30
        (150, 180),         # 12:30-13:00
        (210, 270),         # 13:30-14:30
        (270, 360),         # 15:30-17:00
        # Thursday
        (60, 150),          # 9:30-11:30
        (180, 240),         # 12:00-14:00
        (240, 270),         # 13:30-14:00
        (270, 300),         # 14:30-15:00
        (300, 360),         # 15:30-16:30
        # Friday
        (0, 1080)           # 9:00-17:00
    ]
    
    max_time = 1080        # 17:00
    earliest_start = 0     # 9:00
    latest_start = 480     # 16:00
    
    # Define the context
    ctx = z3.Context()
    
    # Variable for the start time in minutes (0 to 1080)
    s = z3.Int(ctx, "s")
    
    # Add constraints for Betty's schedule
    for a, b in betty_intervals:
        constraint = (s + 60) <= a | (b <= s)
        ctx.add(constraint)
    
    # Add constraints for Megan's schedule
    for a, b in megan_intervals:
        constraint = (s + 60) <= a | (b <= s)
        ctx.add(constraint)
    
    # Ensure the meeting does not occur on Wednesday or Thursday
    ctx.add((day == 2) | (day == 3))
    
    # Ensure the meeting starts after 9:00 and ends by 17:00
    ctx.add(s >= earliest_start)
    ctx.add(s + 60 <= max_time)
    
    # Solve the problem
    result = ctx.solve()
    
    if result:
        # Convert s to time string
        start_min = result.model[s]
        start_h = start_min // 60
        start_m = start_min % 60
        start_time = f"{start_h:02d}:{start_m:02d}"
        end_min = start_min + 60
        end_h = end_min // 60
        end_m = end_min % 60
        end_time = f"{end_h:02d}:{end_m:02d}"
        day_str = day_options[result.model[day]]
        return (day_str, start_time, end_time)
    else:
        return None

solve_scheduling()