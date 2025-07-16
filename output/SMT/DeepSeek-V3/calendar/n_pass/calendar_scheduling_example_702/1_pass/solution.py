from z3 import *

def solve_scheduling():
    # Create the solver
    solver = Solver()
    
    # Define variables
    day = Int('day')  # 0: Monday, 1: Tuesday, 2: Wednesday
    start_time = Int('start_time')  # in minutes from 00:00
    end_time = Int('end_time')
    
    # Meeting duration is 30 minutes
    solver.add(end_time == start_time + 30)
    
    # Work hours are 9:00 to 17:00 (540 to 1020 minutes)
    solver.add(start_time >= 540)
    solver.add(end_time <= 1020)
    
    # Day must be 0, 1, or 2
    solver.add(day >= 0, day <= 2)
    
    # Robert's existing meetings
    # Each entry is (day, start, end)
    robert_meetings = [
        (0, 660, 690),   # Monday 11:00-11:30
        (0, 840, 870),   # Monday 14:00-14:30
        (0, 930, 960),   # Monday 15:30-16:00
        (1, 630, 660),   # Tuesday 10:30-11:00
        (1, 900, 930),   # Tuesday 15:00-15:30
        (2, 600, 660),   # Wednesday 10:00-11:00
        (2, 690, 720),   # Wednesday 11:30-12:00
        (2, 750, 780),   # Wednesday 12:30-13:00
        (2, 810, 840),   # Wednesday 13:30-14:00
        (2, 900, 930),   # Wednesday 15:00-15:30
        (2, 960, 990)    # Wednesday 16:00-16:30
    ]
    
    # Ralph's existing meetings
    ralph_meetings = [
        (0, 600, 810),   # Monday 10:00-13:30
        (0, 840, 870),   # Monday 14:00-14:30
        (0, 900, 1020),   # Monday 15:00-17:00
        (1, 540, 570),    # Tuesday 9:00-9:30
        (1, 600, 630),    # Tuesday 10:00-10:30
        (1, 660, 690),    # Tuesday 11:00-11:30
        (1, 720, 780),    # Tuesday 12:00-13:00
        (1, 840, 930),    # Tuesday 14:00-15:30
        (1, 960, 1020),   # Tuesday 16:00-17:00
        (2, 630, 660),    # Wednesday 10:30-11:00
        (2, 690, 720),    # Wednesday 11:30-12:00
        (2, 780, 870),     # Wednesday 13:00-14:30
        (2, 990, 1020)     # Wednesday 16:30-17:00
    ]
    
    # Constraint: The meeting does not overlap with any of Robert's meetings on the selected day
    robert_constraints = []
    for d, s, e in robert_meetings:
        robert_constraints.append(Or(day != d, end_time <= s, start_time >= e))
    solver.add(And(robert_constraints))
    
    # Constraint: The meeting does not overlap with any of Ralph's meetings on the selected day
    ralph_constraints = []
    for d, s, e in ralph_meetings:
        ralph_constraints.append(Or(day != d, end_time <= s, start_time >= e))
    solver.add(And(ralph_constraints))
    
    # Robert prefers to avoid more meetings on Monday, so prioritize Tuesday and Wednesday
    # We can add a soft constraint to prefer days other than Monday
    # But for exact solution, we can first try Tuesday and Wednesday, then Monday
    # Alternatively, we can find all solutions and pick the earliest one that's not Monday
    
    # To find the earliest possible time, we'll minimize start_time
    # We can use an Optimize solver for this
    opt = Optimize()
    opt.add(solver.assertions())
    opt.minimize(start_time)
    
    # Also, prefer days other than Monday (day 0)
    # We can add a soft constraint to minimize the day (since Monday is 0, Tuesday 1, etc.)
    # Or, we can find solutions in order of preference: Tuesday, Wednesday, Monday
    # Here, we'll first try to find solutions where day != 0, then if not found, day = 0
    
    # Check if there's a solution with day != 0 (Tuesday or Wednesday)
    temp_solver = Solver()
    temp_solver.add(solver.assertions())
    temp_solver.add(day != 0)
    if temp_solver.check() == sat:
        model = temp_solver.model()
    else:
        # Check with day = 0 (Monday)
        temp_solver = Solver()
        temp_solver.add(solver.assertions())
        temp_solver.add(day == 0)
        if temp_solver.check() == sat:
            model = temp_solver.model()
        else:
            print("No solution found")
            return
    
    # Extract the solution
    day_val = model[day].as_long()
    start_val = model[start_time].as_long()
    end_val = model[end_time].as_long()
    
    # Convert day_val to day name
    days = ["Monday", "Tuesday", "Wednesday"]
    day_name = days[day_val]
    
    # Convert start and end times to HH:MM format
    start_h = start_val // 60
    start_m = start_val % 60
    end_h = end_val // 60
    end_m = end_val % 60
    
    print(f"SOLUTION:")
    print(f"Day: {day_name}")
    print(f"Start Time: {start_h:02d}:{start_m:02d}")
    print(f"End Time: {end_h:02d}:{end_m:02d}")

solve_scheduling()