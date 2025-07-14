from z3 import *

def solve_scheduling():
    # Initialize the solver
    solver = Solver()
    
    # Define variables
    day = Int('day')  # 0: Monday, 1: Tuesday, 2: Wednesday
    start_time = Int('start_time')  # in minutes from 00:00 (e.g., 9:00 is 540)
    end_time = Int('end_time')
    
    # Define day constraints (0, 1, 2 for Monday, Tuesday, Wednesday)
    solver.add(day >= 0, day <= 2)
    
    # Meeting duration is 30 minutes
    solver.add(end_time == start_time + 30)
    
    # Work hours are 9:00 (540) to 17:00 (1020)
    solver.add(start_time >= 540, end_time <= 1020)
    
    # Joshua's busy slots per day (each slot is (day, start, end))
    joshua_busy = [
        (0, 15*60, 15*60 + 30),  # Monday 15:00-15:30
        (1, 11*60 + 30, 12*60),    # Tuesday 11:30-12:00
        (1, 13*60, 13*60 + 30),    # Tuesday 13:00-13:30
        (1, 14*60 + 30, 15*60)     # Tuesday 14:30-15:00
    ]
    
    # Joyce's busy slots per day
    joyce_busy = [
        (0, 9*60, 9*60 + 30),      # Monday 9:00-9:30
        (0, 10*60, 11*60),         # Monday 10:00-11:00
        (0, 11*60 + 30, 12*60 + 30), # Monday 11:30-12:30
        (0, 13*60, 15*60),         # Monday 13:00-15:00
        (0, 15*60 + 30, 17*60),    # Monday 15:30-17:00
        (1, 9*60, 17*60),          # Tuesday 9:00-17:00 (entire day)
        (2, 9*60, 9*60 + 30),      # Wednesday 9:00-9:30
        (2, 10*60, 11*60),         # Wednesday 10:00-11:00
        (2, 12*60 + 30, 15*60 + 30), # Wednesday 12:30-15:30
        (2, 16*60, 16*60 + 30)     # Wednesday 16:00-16:30
    ]
    
    # Constraints for Joshua's busy times
    for (d, s, e) in joshua_busy:
        solver.add(Not(And(day == d, start_time < e, end_time > s)))
    
    # Constraints for Joyce's busy times
    for (d, s, e) in joyce_busy:
        solver.add(Not(And(day == d, start_time < e, end_time > s)))
    
    # Joyce prefers not to meet on Monday before 12:00 (720 minutes)
    solver.add(Not(And(day == 0, start_time < 720)))
    
    # Check if a solution exists
    if solver.check() == sat:
        model = solver.model()
        day_val = model[day].as_long()
        start_val = model[start_time].as_long()
        end_val = model[end_time].as_long()
        
        # Convert day_val to day name
        days = ["Monday", "Tuesday", "Wednesday"]
        day_name = days[day_val]
        
        # Convert start and end times to HH:MM format
        start_hh = start_val // 60
        start_mm = start_val % 60
        end_hh = end_val // 60
        end_mm = end_val % 60
        
        # Format the output
        solution = f"SOLUTION:\nDay: {day_name}\nStart Time: {start_hh:02d}:{start_mm:02d}\nEnd Time: {end_hh:02d}:{end_mm:02d}"
        print(solution)
    else:
        print("No solution found")

solve_scheduling()