import z3

def solve_scheduling():
    day = "Monday"
    # Convert busy intervals to minutes since 9:00
    james_intervals = [(11*60 + 30, 12*60), (14*60 + 30, 15*60)]
    john_intervals = [(9*60 + 30, 11*60), (11*60 + 30, 12*60), (12*60 + 30, 13*60), (14*60 + 30, 16*60 + 30)]
    
    # Define the context
    ctx = z3.Context()
    
    # Variable for the start time in minutes (0 to 1080)
    s = z3.Int(ctx, "s")
    
    # Add constraints for each interval
    for a, b in james_intervals:
        # Constraint: meeting ends before a or starts after b
        constraint = (s + 60) <= a | (b <= s)
        ctx.add(constraint)
    
    for a, b in john_intervals:
        constraint = (s + 60) <= a | (b <= s)
        ctx.add(constraint)
    
    # Add constraints for s being within the day
    ctx.add(s >= 0)
    ctx.add(s + 60 <= 1080)
    
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
        return (day, start_time, end_time)
    else:
        return None

solve_scheduling()