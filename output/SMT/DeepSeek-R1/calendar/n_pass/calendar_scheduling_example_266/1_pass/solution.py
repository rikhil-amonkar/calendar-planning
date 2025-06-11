from z3 import *

def main():
    # Initialize solver
    s = Solver()
    
    # Define the start time variable (in minutes from 9:00)
    start_time = Int('start_time')
    
    # Meeting duration is 30 minutes
    duration = 30
    
    # Total work day in minutes: 9:00 (0) to 17:00 (480 minutes)
    total_minutes = 480
    
    # Constraint: start_time must be in [0, total_minutes - duration] i.e., [0, 450]
    s.add(start_time >= 0)
    s.add(start_time <= total_minutes - duration)
    
    # Blocked times for each participant in minutes (relative to 9:00)
    blocked_times = {
        'Joe': [(30, 60), (90, 120)],
        'Keith': [(150, 180), (360, 390)],
        'Patricia': [(0, 30), (240, 270)],
        'Nancy': [(0, 120), (150, 450)],
        'Pamela': [(0, 60), (90, 120), (150, 210), (240, 300), (330, 360), (390, 420), (450, 480)]
    }
    
    # For each participant, add constraints that the meeting does not overlap any blocked interval
    for person, intervals in blocked_times.items():
        for (b_start, b_end) in intervals:
            # The meeting must be either entirely before the blocked interval or entirely after
            s.add(Or(
                start_time + duration <= b_start,
                start_time >= b_end
            ))
    
    # Check if a solution exists
    if s.check() == sat:
        model = s.model()
        start_minutes = model.eval(start_time).as_long()
        
        # Convert minutes to HH:MM format
        hours = 9 + start_minutes // 60
        minutes = start_minutes % 60
        start_time_str = f"{hours:02d}:{minutes:02d}"
        end_minutes = start_minutes + duration
        end_hours = 9 + end_minutes // 60
        end_minutes = end_minutes % 60
        end_time_str = f"{end_hours:02d}:{end_minutes:02d}"
        
        print(f"Monday {start_time_str} to {end_time_str}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()