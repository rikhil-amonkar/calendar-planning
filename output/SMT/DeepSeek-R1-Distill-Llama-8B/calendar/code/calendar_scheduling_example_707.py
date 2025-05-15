import z3

def solve_scheduling():
    day_options = ["Monday", "Tuesday", "Wednesday"]
    day = z3.Int("day", "0 to 2")
    
    # Convert busy intervals to minutes since 9:00
    ryan_intervals = [
        # Monday
        (30, 60),   # 9:30-10:00
        (90, 120),  # 11:00-12:00
        (150, 180), # 13:00-13:30
        (270, 300), # 15:30-16:00
        # Tuesday
        (150, 180), # 11:30-12:30
        (270, 300), # 15:30-16:00
        # Wednesday
        (60, 90),   # 12:00-13:00
        (270, 300), # 15:30-16:00
        (330, 360)  # 16:30-17:00
    ]
    adam_intervals = [
        # Monday
        (0, 90),     # 9:00-10:30
        (90, 210),   # 11:00-13:30
        (240, 360),  # 14:00-17:00
        # Tuesday
        (0, 60),     # 9:00-10:00
        (90, 210),   # 10:30-15:30
        (240, 360),  # 16:00-17:00
        # Wednesday
        (0, 30),     # 9:00-9:30
        (60, 90),    # 10:00-11:00
        (90, 150),   # 11:30-14:30
        (180, 210),  # 15:00-15:30
        (240, 270)   # 16:00-16:30
    ]
    
    max_time = 1080        # 17:00
    earliest_start = 0     # 9:00
    latest_start = 480     # 16:00
    
    # Define the context
    ctx = z3.Context()
    
    # Variable for the start time in minutes (0 to 1080)
    s = z3.Int(ctx, "s")
    
    # Add constraints for each interval
    for a, b in ryan_intervals:
        constraint = (s + 30) <= a | (b <= s)
        ctx.add(constraint)
    
    for a, b in adam_intervals:
        constraint = (s + 30) <= a | (b <= s)
        ctx.add(constraint)
    
    # Ensure the meeting does not occur on Wednesday
    ctx.add(day != 2)
    
    # Ensure the meeting starts no later than 14:30 on Monday and 10:30 on Tuesday
    ctx.add((day == 0) & (s <= 240))  # Monday: latest 14:30
    ctx.add((day == 1) & (s <= 150))  # Tuesday: latest 10:30
    
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