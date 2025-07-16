from z3 import *

def solve_scheduling():
    # Initialize the solver
    solver = Solver()
    
    # Define variables
    day = Int('day')  # 0: Monday, 1: Tuesday, 2: Wednesday, 3: Thursday
    start_time = Int('start_time')  # in minutes from 9:00 (540 minutes in 24-hour format)
    
    # Meeting duration is 1 hour (60 minutes)
    duration = 60
    
    # Constraints for day: must be between 0 and 3 (Monday to Thursday)
    solver.add(day >= 0, day <= 3)
    
    # Constraints for start_time: must be between 9:00 (540 minutes) and 17:00 (1020 minutes) minus duration
    solver.add(start_time >= 540, start_time + duration <= 1020)
    
    # Define the busy slots for each participant per day
    # Each entry is (day, start, end) in minutes from 0:00
    natalie_busy = [
        # Monday
        (0, 540, 570),   # 9:00-9:30
        (0, 600, 720),    # 10:00-12:00
        (0, 750, 780),    # 12:30-13:00
        (0, 840, 870),    # 14:00-14:30
        (0, 900, 990),    # 15:00-16:30
        # Tuesday
        (1, 540, 570),   # 9:00-9:30
        (1, 600, 630),    # 10:00-10:30
        (1, 750, 840),    # 12:30-14:00
        (1, 960, 1020),   # 16:00-17:00
        # Wednesday
        (2, 660, 690),    # 11:00-11:30
        (2, 960, 990),    # 16:00-16:30
        # Thursday
        (3, 600, 660),    # 10:00-11:00
        (3, 690, 900),    # 11:30-15:00
        (3, 930, 960),    # 15:30-16:00
        (3, 990, 1020)    # 16:30-17:00
    ]
    
    william_busy = [
        # Monday
        (0, 570, 660),    # 9:30-11:00
        (0, 690, 1020),   # 11:30-17:00
        # Tuesday
        (1, 540, 780),    # 9:00-13:00
        (1, 810, 960),    # 13:30-16:00
        # Wednesday
        (2, 540, 750),    # 9:00-12:30
        (2, 780, 870),    # 13:00-14:30
        (2, 930, 960),    # 15:30-16:00
        (2, 990, 1020),   # 16:30-17:00
        # Thursday
        (3, 540, 630),    # 9:00-10:30
        (3, 660, 690),    # 11:00-11:30
        (3, 720, 750),    # 12:00-12:30
        (3, 780, 840),    # 13:00-14:00
        (3, 900, 1020)    # 15:00-17:00
    ]
    
    # For the selected day, the meeting must not overlap with any busy slot for Natalie or William
    for d, s, e in natalie_busy:
        # If the meeting is on day 'd', then it must not overlap with (s, e)
        solver.add(Implies(day == d, Or(start_time >= e, start_time + duration <= s)))
    
    for d, s, e in william_busy:
        solver.add(Implies(day == d, Or(start_time >= e, start_time + duration <= s)))
    
    # Check if there's a solution
    if solver.check() == sat:
        model = solver.model()
        day_val = model[day].as_long()
        start_val = model[start_time].as_long()
        
        # Convert day_val to day name
        days = ["Monday", "Tuesday", "Wednesday", "Thursday"]
        day_name = days[day_val]
        
        # Convert start_val to HH:MM format
        start_hour = start_val // 60
        start_min = start_val % 60
        start_time_str = f"{start_hour:02d}:{start_min:02d}"
        
        end_val = start_val + duration
        end_hour = end_val // 60
        end_min = end_val % 60
        end_time_str = f"{end_hour:02d}:{end_min:02d}"
        
        # Prepare the solution output
        solution = f"SOLUTION:\nDay: {day_name}\nStart Time: {start_time_str}\nEnd Time: {end_time_str}"
        print(solution)
    else:
        print("No solution found")

solve_scheduling()