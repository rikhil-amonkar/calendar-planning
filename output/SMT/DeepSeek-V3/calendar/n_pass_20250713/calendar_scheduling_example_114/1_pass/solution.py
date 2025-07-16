from z3 import *

def solve_meeting_schedule():
    # Define the participants' busy times in minutes since midnight
    # Each entry is (start_minute, end_minute)
    stephanie_busy = [(10*60, 10*60 + 30), (16*60, 16*60 + 30)]
    cheryl_busy = [(10*60, 10*60 + 30), (11*60 + 30, 12*60), 
                   (13*60 + 30, 14*60), (16*60 + 30, 17*60)]
    bradley_busy = [(9*60 + 30, 10*60), (10*60 + 30, 11*60 + 30),
                    (13*60 + 30, 14*60), (14*60 + 30, 15*60),
                    (15*60 + 30, 17*60)]
    steven_busy = [(9*60, 12*60), (13*60, 13*60 + 30),
                   (14*60 + 30, 17*60)]
    
    all_busy = stephanie_busy + cheryl_busy + bradley_busy + steven_busy
    
    # Create a Z3 solver instance
    s = Solver()
    
    # Define the start time variable (in minutes)
    start_time = Int('start_time')
    
    # Meeting duration is 1 hour (60 minutes)
    duration = 60
    end_time = start_time + duration
    
    # Constraints:
    # 1. Meeting must be within work hours (9:00 to 17:00)
    s.add(start_time >= 9 * 60)
    s.add(end_time <= 17 * 60)
    
    # 2. Meeting must not overlap with any busy times
    for busy_start, busy_end in all_busy:
        s.add(Or(
            end_time <= busy_start,  # Meeting ends before busy time starts
            start_time >= busy_end   # Meeting starts after busy time ends
        ))
    
    # Check if there's a solution
    if s.check() == sat:
        model = s.model()
        start_min = model[start_time].as_long()
        
        # Convert minutes back to HH:MM format
        start_hh = start_min // 60
        start_mm = start_min % 60
        end_min = start_min + duration
        end_hh = end_min // 60
        end_mm = end_min % 60
        
        # Format the output
        solution = (
            f"SOLUTION:\n"
            f"Day: Monday\n"
            f"Start Time: {start_hh:02d}:{start_mm:02d}\n"
            f"End Time: {end_hh:02d}:{end_mm:02d}"
        )
        print(solution)
    else:
        print("No solution found.")

solve_meeting_schedule()