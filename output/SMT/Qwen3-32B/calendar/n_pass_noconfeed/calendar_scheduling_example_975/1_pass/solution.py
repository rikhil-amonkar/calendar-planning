from z3 import *

def schedule_meeting():
    # Define busy intervals for each participant per day
    nicole_busy = [
        [],  # Monday
        [(960, 990)],  # Tuesday
        [(900, 930)],  # Wednesday
        [],  # Thursday
        [(720, 750), (930, 960)],  # Friday
    ]
    daniel_busy = [
        [(540, 750), (780, 810), (840, 990)],  # Monday
        [(540, 630), (690, 750), (780, 810), (900, 960), (990, 1020)],  # Tuesday
        [(540, 600), (660, 750), (780, 810), (840, 870), (990, 1020)],  # Wednesday
        [(660, 720), (780, 840), (900, 930)],  # Thursday
        [(600, 660), (690, 720), (750, 870), (900, 930), (960, 990)],  # Friday
    ]
    days = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]
    
    day = Int('day')
    start = Int('start')
    
    s = Optimize()
    
    # Constraints on day and start
    s.add(And(day >= 0, day <= 4))
    s.add(And(start >= 540, start <= 960))
    
    # For each day d, and each busy interval of Nicole and Daniel on that day, add constraints
    for d in range(5):
        for (s_n, e_n) in nicole_busy[d]:
            # If day == d, then start must not conflict with Nicole's interval (s_n, e_n)
            s.add(Or(day != d, Or(start + 60 <= s_n, start >= e_n)))
        for (s_d, e_d) in daniel_busy[d]:
            s.add(Or(day != d, Or(start + 60 <= s_d, start >= e_d)))
    
    # Objective: minimize the total minutes since the start of the week
    s.minimize(day * 1440 + start)
    
    if s.check() == sat:
        m = s.model()
        day_val = m[day].as_long()
        start_time = m[start].as_long()
        end_time = start_time + 60
        # Convert to time strings
        start_h = start_time // 60
        start_m = start_time % 60
        end_h = end_time // 60
        end_m = end_time % 60
        start_str = f"{start_h:02d}:{start_m:02d}"
        end_str = f"{end_h:02d}:{end_m:02d}"
        day_name = days[day_val]
        print(f"{start_str}:{end_str} {day_name}")
    else:
        print("No solution found")

schedule_meeting()