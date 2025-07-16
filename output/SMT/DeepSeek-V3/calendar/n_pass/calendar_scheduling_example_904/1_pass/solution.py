from z3 import *

def solve_scheduling():
    # Initialize Z3 solver
    solver = Solver()
    
    # Days: 0=Monday, 1=Tuesday, 2=Wednesday, 3=Thursday, 4=Friday
    day = Int('day')
    start_time_min = Int('start_time_min')  # in minutes since midnight
    
    # Meeting duration is 30 minutes
    meeting_duration = 30
    end_time_min = start_time_min + meeting_duration
    
    # Work hours are 9:00 (540) to 17:00 (1020)
    solver.add(day >= 0, day <= 4)
    solver.add(start_time_min >= 540)
    solver.add(end_time_min <= 1020)
    
    # Daniel's busy slots per day
    daniel_busy = {
        0: [(570, 630), (720, 750), (780, 840), (870, 900), (930, 960)],  # Monday
        1: [(660, 720), (780, 810), (930, 960), (990, 1020)],             # Tuesday
        2: [(540, 600), (840, 870)],                                      # Wednesday
        3: [(630, 660), (720, 780), (870, 900), (930, 960)],              # Thursday
        4: [(540, 570), (690, 720), (780, 810), (990, 1020)]              # Friday
    }
    
    # Bradley's busy slots per day
    bradley_busy = {
        0: [(570, 660), (690, 720), (750, 780), (840, 900)],              # Monday
        1: [(630, 660), (720, 780), (810, 840), (930, 990)],              # Tuesday
        2: [(540, 600), (660, 780), (810, 840), (870, 1020)],            # Wednesday
        3: [(540, 750), (810, 840), (870, 900), (930, 990)],             # Thursday
        4: [(540, 570), (600, 750), (780, 810), (840, 870), (930, 990)]  # Friday
    }
    
    # Constraints for Daniel's busy slots
    for d in daniel_busy:
        for (busy_start, busy_end) in daniel_busy[d]:
            solver.add(Not(And(day == d, 
                              start_time_min < busy_end, 
                              end_time_min > busy_start)))
    
    # Constraints for Bradley's busy slots
    for d in bradley_busy:
        for (busy_start, busy_end) in bradley_busy[d]:
            solver.add(Not(And(day == d, 
                              start_time_min < busy_end, 
                              end_time_min > busy_start)))
    
    # Daniel's preferences: not Wednesday, not Thursday
    solver.add(day != 2)  # Wednesday
    solver.add(day != 3)  # Thursday
    
    # Bradley's preferences: not Monday, not Tuesday before 12:00, not Friday
    solver.add(day != 0)  # Monday
    solver.add(Not(And(day == 1, start_time_min < 720)))  # Tuesday before 12:00 (720 minutes)
    solver.add(day != 4)  # Friday
    
    # Check for a solution
    if solver.check() == sat:
        model = solver.model()
        day_val = model[day].as_long()
        start_min_val = model[start_time_min].as_long()
        
        # Convert day_val to day name
        days = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]
        day_name = days[day_val]
        
        # Convert start_min_val to HH:MM format
        start_hh = start_min_val // 60
        start_mm = start_min_val % 60
        start_time = f"{start_hh:02d}:{start_mm:02d}"
        
        # Calculate end time
        end_min_val = start_min_val + 30
        end_hh = end_min_val // 60
        end_mm = end_min_val % 60
        end_time = f"{end_hh:02d}:{end_mm:02d}"
        
        # Output the solution
        print("SOLUTION:")
        print(f"Day: {day_name}")
        print(f"Start Time: {start_time}")
        print(f"End Time: {end_time}")
    else:
        print("No solution found")

solve_scheduling()