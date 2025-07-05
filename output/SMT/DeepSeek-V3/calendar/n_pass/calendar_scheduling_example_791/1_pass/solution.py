from z3 import *

def solve_scheduling():
    # Create the solver
    s = Solver()
    
    # Define the possible days (0: Monday, 1: Tuesday, 2: Wednesday)
    day = Int('day')
    s.add(day >= 0, day <= 2)
    
    # Define the start time in minutes from 9:00 (540 minutes)
    start_time = Int('start_time')
    s.add(start_time >= 540, start_time <= 1020 - 30)  # 17:00 is 1020 minutes
    
    # End time is start time + 30 minutes
    end_time = start_time + 30
    
    # Nicole's busy times in minutes from 9:00 for each day
    nicole_busy = {
        0: [(540, 570), (780, 810), (870, 930)],  # Monday
        1: [(540, 570), (750, 870), (870, 930)],  # Tuesday
        2: [(600, 660), (750, 900), (960, 1020)]  # Wednesday
    }
    
    # Ruth's busy times in minutes from 9:00 for each day
    ruth_busy = {
        0: [(540, 1020)],  # Monday (entire day)
        1: [(540, 1020)],  # Tuesday (entire day)
        2: [(540, 630), (660, 690), (720, 750), (810, 930), (960, 990)]  # Wednesday
    }
    
    # Ruth does not want to meet on Wednesday after 13:30 (810 minutes)
    s.add(Not(And(day == 2, start_time >= 810)))
    
    # Function to check if a time interval overlaps with any busy intervals
    def is_busy(time_day, busy_intervals):
        overlaps = Or([And(start_time < end, end_time > start) for (start, end) in busy_intervals])
        return And(day == time_day, overlaps)
    
    # Add constraints for Nicole's availability
    s.add(Not(Or([is_busy(d, intervals) for d, intervals in nicole_busy.items()])))
    
    # Add constraints for Ruth's availability
    s.add(Not(Or([is_busy(d, intervals) for d, intervals in ruth_busy.items()])))
    
    # Check for a solution
    if s.check() == sat:
        m = s.model()
        day_val = m[day].as_long()
        start_val = m[start_time].as_long()
        
        # Convert day to string
        days = ["Monday", "Tuesday", "Wednesday"]
        day_str = days[day_val]
        
        # Convert start time to HH:MM
        start_h = start_val // 60
        start_m = start_val % 60
        start_time_str = f"{start_h:02d}:{start_m:02d}"
        
        # Convert end time to HH:MM
        end_h = (start_val + 30) // 60
        end_m = (start_val + 30) % 60
        end_time_str = f"{end_h:02d}:{end_m:02d}"
        
        # Print the solution
        print("SOLUTION:")
        print(f"Day: {day_str}")
        print(f"Start Time: {start_time_str}")
        print(f"End Time: {end_time_str}")
    else:
        print("No solution found")

solve_scheduling()