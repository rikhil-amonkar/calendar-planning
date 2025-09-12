from z3 import *

def main():
    # Initialize solver
    solver = Solver()
    
    # Define variables
    day = Int('day')
    start_minute = Int('start_minute')
    
    # Meeting duration in minutes
    duration = 60
    
    # Work hours: 9:00 to 17:00 (540 to 1020 minutes)
    work_start = 540
    work_end = 1020
    
    # Day mapping: 0=Monday, 1=Tuesday, 2=Wednesday, 3=Thursday
    days = ['Monday', 'Tuesday', 'Wednesday', 'Thursday']
    
    # Laura's busy intervals (day, start_minute, end_minute)
    laura_busy = [
        (0, 630, 660),   # Monday 10:30-11:00
        (0, 750, 780),   # Monday 12:30-13:00
        (0, 870, 930),   # Monday 14:30-15:30
        (0, 960, 1020),  # Monday 16:00-17:00
        (1, 570, 600),   # Tuesday 9:30-10:00
        (1, 660, 690),   # Tuesday 11:00-11:30
        (1, 780, 810),   # Tuesday 13:00-13:30
        (1, 870, 900),   # Tuesday 14:30-15:00
        (1, 960, 1020),  # Tuesday 16:00-17:00
        (2, 690, 720),   # Wednesday 11:30-12:00
        (2, 750, 780),   # Wednesday 12:30-13:00
        (2, 930, 990),   # Wednesday 15:30-16:30
        (3, 630, 660),   # Thursday 10:30-11:00
        (3, 720, 810),   # Thursday 12:00-13:30
        (3, 900, 930),   # Thursday 15:00-15:30
        (3, 960, 990)    # Thursday 16:00-16:30
    ]
    
    # Philip's busy intervals (day, start_minute, end_minute)
    philip_busy = [
        (0, 540, 1020),  # Monday 9:00-17:00
        (1, 540, 660),   # Tuesday 9:00-11:00
        (1, 690, 720),   # Tuesday 11:30-12:00
        (1, 780, 810),   # Tuesday 13:00-13:30
        (1, 840, 870),   # Tuesday 14:00-14:30
        (1, 900, 990),   # Tuesday 15:00-16:30
        (2, 540, 600),   # Wednesday 9:00-10:00
        (2, 660, 720),   # Wednesday 11:00-12:00
        (2, 750, 960),   # Wednesday 12:30-16:00
        (2, 990, 1020),  # Wednesday 16:30-17:00
        (3, 540, 630),   # Thursday 9:00-10:30
        (3, 660, 750),   # Thursday 11:00-12:30
        (3, 780, 1020)   # Thursday 13:00-17:00
    ]
    
    # Constraints
    # Day must be Monday (0), Tuesday (1), or Thursday (3) (Philip cannot meet Wednesday)
    solver.add(Or(day == 0, day == 1, day == 3))
    # Start time must be within work hours and allow full meeting duration
    solver.add(start_minute >= work_start)
    solver.add(start_minute <= work_end - duration)
    
    # Laura availability constraints
    for d, s, e in laura_busy:
        # If meeting is on this day, it must not overlap with busy interval
        solver.add(Implies(day == d, Not(And(start_minute < e, start_minute + duration > s))))
    
    # Philip availability constraints
    for d, s, e in philip_busy:
        solver.add(Implies(day == d, Not(And(start_minute < e, start_minute + duration > s))))
    
    # Check for solution
    if solver.check() == sat:
        model = solver.model()
        d_val = model[day].as_long()
        start_val = model[start_minute].as_long()
        
        # Calculate end time
        end_val = start_val + duration
        
        # Convert minutes to time strings
        def minutes_to_time(minutes):
            hours = minutes // 60
            mins = minutes % 60
            return f"{hours}:{mins:02d}"
        
        start_str = minutes_to_time(start_val)
        end_str = minutes_to_time(end_val)
        
        # Output day and time range
        print(f"{days[d_val]} {start_str}:{end_str}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()