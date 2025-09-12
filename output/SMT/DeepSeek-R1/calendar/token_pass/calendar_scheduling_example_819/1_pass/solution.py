from z3 import *

def main():
    # Create solver
    solver = Solver()
    
    # Define variables
    day = Int('day')
    start_time = Int('start_time')  # in minutes from 9:00
    
    # Constants
    duration = 30
    min_time = 0
    max_time = 8 * 60 - duration  # 17:00 is 8*60=480 minutes from 9:00
    
    # Day and time constraints
    solver.add(day >= 0, day <= 3)
    solver.add(start_time >= min_time, start_time <= max_time)
    
    # Busy intervals for Ruth per day (in minutes from 9:00)
    busy_intervals = {
        0: [(0, 480)],  # Monday (all day)
        1: [(0, 480)],  # Tuesday (all day)
        2: [(0, 480)],  # Wednesday (all day)
        3: [(0, 120), (150, 330), (360, 480)]  # Thursday
    }
    
    # Julie's constraint: Avoid Thursday before 11:30 (150 minutes from 9:00)
    solver.add(If(day == 3, start_time >= 150, True))
    
    # Add constraints for Ruth's busy times
    for d, intervals in busy_intervals.items():
        for interval in intervals:
            busy_start, busy_end = interval
            # Meeting must not overlap with busy interval
            solver.add(If(day == d,
                          Not(And(start_time < busy_end, start_time + duration > busy_start)),
                          True))
    
    # Check for solution
    if solver.check() == sat:
        model = solver.model()
        d = model[day].as_long()
        s = model[start_time].as_long()
        
        # Convert start time to HH:MM
        start_hour = 9 + s // 60
        start_minute = s % 60
        end_time = s + duration
        end_hour = 9 + end_time // 60
        end_minute = end_time % 60
        
        # Format time string
        time_str = f"{start_hour:02d}:{start_minute:02d}:{end_hour:02d}:{end_minute:02d}"
        
        # Map day index to name
        days = ["Monday", "Tuesday", "Wednesday", "Thursday"]
        day_str = days[d]
        
        print(f"{day_str} {time_str}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()