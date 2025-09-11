from z3 import *

def main():
    # Initialize solver
    solver = Solver()
    
    # Meeting duration in minutes
    duration = 30
    
    # Work hours: 9:00 to 17:00 (8 hours = 480 minutes)
    total_minutes = 480
    max_start = total_minutes - duration
    
    # Start time variable (in minutes from 9:00)
    start = Int('start')
    solver.add(start >= 0, start <= max_start)
    
    # Busy intervals in minutes from 9:00
    busy_intervals = [
        # Stephanie
        [(120, 150), (330, 360)],
        # Joe
        [(0, 30), (60, 180), (210, 240), (300, 480)],
        # Diana
        [(0, 90), (150, 180), (240, 300), (330, 390), (420, 480)],
        # Deborah
        [(0, 60), (90, 180), (210, 240), (270, 300), (330, 390), (420, 450)]
    ]
    
    # Add constraints for each participant's busy intervals
    for intervals in busy_intervals:
        for (b_start, b_end) in intervals:
            # Meeting must not overlap with busy interval
            solver.add(Or(start + duration <= b_start, start >= b_end))
    
    # Check for a solution
    if solver.check() == sat:
        model = solver.model()
        start_val = model.evaluate(start).as_long()
        
        # Convert start and end times to HH:MM format
        start_hour = 9 + start_val // 60
        start_minute = start_val % 60
        end_time = start_val + duration
        end_hour = 9 + end_time // 60
        end_minute = end_time % 60
        
        # Format the time string
        time_str = f"{start_hour:02d}:{start_minute:02d}-{end_hour:02d}:{end_minute:02d}"
        print(f"Monday {time_str}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()