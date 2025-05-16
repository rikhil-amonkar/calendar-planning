import z3

def solve_scheduling():
    day_options = ["Monday", "Tuesday", "Wednesday", "Thursday"]
    day = z3.Int("day", "0 to 3")
    
    # Convert busy intervals to minutes since 9:00
    mary_intervals = [
        # Tuesday
        (90, 120),        # 10:00-10:30
        (270, 300),       # 15:30-16:00
        # Wednesday
        (30, 60),         # 9:30-10:00
        (210, 240),       # 15:00-15:30
        # Thursday
        (0, 30),          # 9:00-10:00
        (90, 150)         # 10:30-11:30
    ]
    alexis_intervals = [
        # Monday
        (0, 60),           # 9:00-10:00
        (90, 180),         # 10:30-12:00
        (210, 360),        # 12:30-17:00
        # Tuesday
        (0, 60),           # 9:00-10:00
        (90, 150),         # 10:30-11:30
        (120, 270),        # 12:00-15:30
        (240, 360),        # 16:00-17:00
        # Wednesday
        (0, 150),          # 9:00-11:00
        (150, 360),        # 11:30-17:00
        # Thursday
        (60, 120),         # 10:00-12:00
        (120, 150),        # 12:00-13:00
        (150, 180),        # 14:00-14:30
        (180, 240),        # 15:00-16:00
        (240, 360)         # 15:30-17:00
    ]
    
    max_time = 1080        # 17:00
    earliest_start = 0     # 9:00
    latest_start = 480     # 16:00
    
    # Define the context
    ctx = z3.Context()
    
    # Variable for the start time in minutes (0 to 1080)
    s = z3.Int(ctx, "s")
    
    # Add constraints for each interval
    for a, b in mary_intervals:
        constraint = (s + 30) <= a | (b <= s)
        ctx.add(constraint)
    
    for a, b in alexis_intervals:
        constraint = (s + 30) <= a | (b <= s)
        ctx.add(constraint)
    
    # Ensure the meeting does not occur after 16:30 on Monday or Wednesday
    ctx.add((day == 0) | (day == 2) & (s <= 480))
    
    # Ensure the meeting starts no later than 10:30 on Tuesday, Wednesday, or Thursday
    ctx.add((day == 1) | (day == 2) | (day == 3) & (s <= 150))
    
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