from z3 import *

def solve_scheduling():
    # Initialize the solver
    s = Solver()
    
    # Days: 0=Monday, 1=Tuesday, 2=Wednesday, 3=Thursday, 4=Friday
    day = Int('day')
    start_time = Int('start_time')  # minutes from 9:00 (e.g., 0 = 9:00, 30 = 9:30, etc.)
    
    # Constraints for day and start_time
    s.add(day >= 0, day <= 4)
    s.add(start_time >= 0, start_time <= 480 - 30)  # 17:00 is 480 minutes from 9:00
    
    # Meeting duration is 30 minutes
    end_time = start_time + 30
    
    # Define busy slots for Terry and Frances
    # Each entry is (day, start_min, end_min)
    terry_busy = [
        # Monday
        (0, 90, 120), (0, 210, 300), (0, 360, 480),
        # Tuesday
        (1, 30, 60), (1, 90, 120), (1, 300, 330), (1, 420, 450),
        # Wednesday
        (2, 30, 90), (2, 120, 180), (2, 240, 270), (2, 360, 420), (2, 450, 480),
        # Thursday
        (3, 30, 60), (3, 180, 210), (3, 240, 330), (3, 420, 450),
        # Friday
        (4, 0, 150), (4, 180, 210), (4, 270, 420), (4, 450, 480)
    ]
    
    frances_busy = [
        # Monday
        (0, 30, 120), (0, 150, 240), (0, 300, 330), (0, 360, 420),
        # Tuesday
        (1, 0, 30), (1, 60, 90), (1, 120, 180), (1, 240, 330), (1, 390, 450),
        # Wednesday
        (2, 30, 60), (2, 90, 120), (2, 150, 420), (2, 450, 480),
        # Thursday
        (3, 120, 210), (3, 330, 480),
        # Friday
        (4, 30, 90), (4, 120, 210), (4, 240, 420), (4, 450, 480)
    ]
    
    # Add constraints that the meeting does not overlap with any busy slot
    for (busy_day, busy_start, busy_end) in terry_busy:
        s.add(Not(And(day == busy_day,
                      start_time < busy_end,
                      end_time > busy_start)))
    
    for (busy_day, busy_start, busy_end) in frances_busy:
        s.add(Not(And(day == busy_day,
                      start_time < busy_end,
                      end_time > busy_start)))
    
    # Frances prefers to avoid Tuesday, so add a soft constraint
    # We'll first try to find a solution not on Tuesday, and if not found, allow Tuesday
    temp_solver = Solver()
    temp_solver.add(s.assertions())
    temp_solver.add(day != 1)  # Not Tuesday
    
    result = temp_solver.check()
    if result == sat:
        m = temp_solver.model()
    else:
        # If no solution excluding Tuesday, try including Tuesday
        s.check()
        m = s.model()
    
    # Extract the solution
    day_val = m[day].as_long()
    start_val = m[start_time].as_long()
    
    # Convert day and time to readable format
    days = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]
    day_str = days[day_val]
    
    start_hour = 9 + start_val // 60
    start_min = start_val % 60
    end_hour = 9 + (start_val + 30) // 60
    end_min = (start_val + 30) % 60
    
    # Format the output
    print("SOLUTION:")
    print(f"Day: {day_str}")
    print(f"Start Time: {start_hour:02d}:{start_min:02d}")
    print(f"End Time: {end_hour:02d}:{end_min:02d}")

solve_scheduling()