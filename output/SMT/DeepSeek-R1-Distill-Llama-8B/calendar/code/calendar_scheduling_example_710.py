import z3

def solve_scheduling():
    day_options = ["Monday", "Tuesday", "Wednesday"]
    day = z3.Int("day", "0 to 2")
    
    # Convert busy intervals to minutes since 9:00
    cheryl_intervals = [
        # Monday
        (0, 30),          # 9:00-9:30
        (90, 150),        # 11:30-13:00
        (210, 240),       # 15:30-16:00
    ]
    cheryl_tuesday = [
        (180, 210)         # 15:00-15:30
    ]
    
    kyle_intervals = [
        # Monday
        (0, 1080),          # 9:00-17:00
        # Tuesday
        (30, 1080),          # 9:30-17:00
        # Wednesday
        (0, 30),            # 9:00-9:30
        (60, 180),          # 10:00-13:00
        (210, 240),         # 13:30-14:00
        (270, 1080)         # 14:30-17:00
    ]
    
    max_time = 1080        # 17:00
    earliest_start = 0     # 9:00
    
    # Define the context
    ctx = z3.Context()
    
    # Variable for the start time in minutes (0 to 1080)
    s = z3.Int(ctx, "s")
    
    # Add constraints for Cheryl's schedule
    for a, b in cheryl_intervals:
        constraint = (s + 30) <= a | (b <= s)
        ctx.add(constraint)
    
    for a, b in cheryl_tuesday:
        constraint = (s + 30) <= a | (b <= s)
        ctx.add(constraint)
    
    # Add constraints for Kyle's schedule
    for a, b in kyle_intervals:
        constraint = (s + 30) <= a | (b <= s)
        ctx.add(constraint)
    
    # Ensure Cheryl is not meeting on Wednesday
    ctx.add(day != 2)
    
    # Ensure the meeting starts after 9:00 and ends by 17:00
    ctx.add(s >= earliest_start)
    ctx.add(s + 30 <= max_time)
    
    # Solve the problem
    result = ctx.solve()
    
    if result:
        # Convert day and s to time strings
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