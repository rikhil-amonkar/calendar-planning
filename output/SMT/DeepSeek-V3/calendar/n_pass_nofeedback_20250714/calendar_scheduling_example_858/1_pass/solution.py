from z3 import *

def solve_scheduling():
    # Create the solver
    s = Solver()
    
    # Define the variables
    # day: 0=Monday, 1=Tuesday, 2=Wednesday, 3=Thursday
    day = Int('day')
    # start_time: minutes from 9:00 (e.g., 0 = 9:00, 60 = 10:00, etc.)
    start_time = Int('start_time')
    
    # Work hours: 9:00 to 17:00 (480 minutes from 9:00)
    work_start = 0  # 9:00
    work_end = 480   # 17:00 (8 hours * 60 minutes)
    meeting_duration = 60  # 1 hour
    
    # Constraints for work hours and meeting duration
    s.add(day >= 0, day <= 3)  # Monday to Thursday
    s.add(start_time >= work_start)
    s.add(start_time + meeting_duration <= work_end)
    
    # Carl's busy slots (day, start_min, end_min)
    carl_busy = [
        (0, 120, 150),   # Monday 11:00-11:30
        (1, 330, 360),    # Tuesday 14:30-15:00
        (2, 60, 150),     # Wednesday 10:00-11:30
        (2, 240, 270),    # Wednesday 13:00-13:30
        (3, 270, 300),    # Thursday 13:30-14:00
        (3, 420, 450),    # Thursday 16:00-16:30
    ]
    
    # Margaret's busy slots (day, start_min, end_min)
    margaret_busy = [
        (0, 0, 90),       # Monday 9:00-10:30
        (0, 120, 480),    # Monday 11:00-17:00
        (1, 30, 180),     # Tuesday 9:30-12:00
        (1, 270, 300),    # Tuesday 13:30-14:00
        (1, 390, 480),    # Tuesday 15:30-17:00
        (2, 30, 180),     # Wednesday 9:30-12:00
        (2, 210, 240),    # Wednesday 12:30-13:00
        (2, 270, 330),    # Wednesday 13:30-14:30
        (2, 360, 480),    # Wednesday 15:00-17:00
        (3, 60, 180),     # Thursday 10:00-12:00
        (3, 210, 300),     # Thursday 12:30-14:00
        (3, 330, 480),     # Thursday 14:30-17:00
    ]
    
    # Add constraints for Carl's busy slots
    for (d, busy_start, busy_end) in carl_busy:
        s.add(Not(And(day == d,
                      start_time < busy_end,
                      start_time + meeting_duration > busy_start)))
    
    # Add constraints for Margaret's busy slots
    for (d, busy_start, busy_end) in margaret_busy:
        s.add(Not(And(day == d,
                      start_time < busy_end,
                      start_time + meeting_duration > busy_start)))
    
    # Carl prefers to avoid Thursday, so prioritize other days
    # We'll first try to find a solution where day != 3 (Thursday)
    temp_solver = Solver()
    temp_solver.add(s.assertions())
    temp_solver.add(day != 3)
    
    solution = None
    if temp_solver.check() == sat:
        m = temp_solver.model()
        solution = (m[day].as_long(), m[start_time].as_long())
    else:
        # If no solution found excluding Thursday, try including Thursday
        if s.check() == sat:
            m = s.model()
            solution = (m[day].as_long(), m[start_time].as_long())
    
    if solution:
        day_map = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday"}
        day_name = day_map[solution[0]]
        start_min = solution[1]
        start_hour = 9 + start_min // 60
        start_minute = start_min % 60
        end_min = start_min + meeting_duration
        end_hour = 9 + end_min // 60
        end_minute = end_min % 60
        
        print("SOLUTION:")
        print(f"Day: {day_name}")
        print(f"Start Time: {start_hour:02d}:{start_minute:02d}")
        print(f"End Time: {end_hour:02d}:{end_minute:02d}")
    else:
        print("No solution found")

solve_scheduling()