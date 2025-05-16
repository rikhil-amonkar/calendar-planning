import z3

def solve_scheduling():
    day_options = ["Monday", "Tuesday"]
    day = z3.Int("day", "0 to 1")
    
    # Convert busy intervals to minutes since 9:00
    harold_monday = [(0, 60), (210, 60 + 300)]  # 9:00-10:00, 10:30-17:00
    harold_tuesday = [(0, 30), (210, 270), (330, 450), (690, 780), (960, 1050)]  # 9:00-9:30, 10:30-11:30, 12:30-13:30, 14:30-15:30, 16:00-17:00
    
    max_time = 1080  # 17:00
    
    # Define the context
    ctx = z3.Context()
    
    # Variable for the start time in minutes (0 to 1080)
    s = z3.Int(ctx, "s")
    
    # Constraints for Harold's schedule
    # Monday constraints
    ctx.add((s >= 0) & (s + 30 <= 60))  # Before 9:00-10:00
    ctx.add((s >= 210) & (s + 30 <= 300))  # 10:30-17:00
    
    # Tuesday constraints
    ctx.add((day == 1) & (s >= 0) & (s + 30 <= 30))  # 9:00-9:30
    ctx.add((day == 1) & (s >= 210) & (s + 30 <= 270))  # 10:30-11:30
    ctx.add((day == 1) & (s >= 330) & (s + 30 <= 450))  # 12:30-13:30
    ctx.add((day == 1) & (s >= 690) & (s + 30 <= 780))  # 14:30-15:30
    ctx.add((day == 1) & (s >= 960) & (s + 30 <= 1050))  # 16:00-17:00
    
    # Harold's preferences
    # Prefer Tuesday
    ctx.add((s + 30) <= 1080)  # Meeting must end by 17:00, which is always true as duration is 30
    ctx.add(day >= 0 & day <= 1)  # Day can be either Monday or Tuesday
    ctx.add(day == 1)  # Prefer to meet on Tuesday
    ctx.add((s <= 480))  # Prefer to meet before 14:30 on Tuesday
    
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