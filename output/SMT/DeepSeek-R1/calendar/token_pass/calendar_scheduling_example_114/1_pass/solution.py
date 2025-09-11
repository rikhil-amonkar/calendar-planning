from z3 import *

def main():
    # Initialize solver
    s = Solver()
    
    # Work hours: 9:00 to 17:00 (540 to 1020 minutes)
    work_start = 540
    work_end = 1020
    duration = 60
    
    # Meeting start time variable (in minutes)
    start = Int('start')
    s.add(start >= work_start)
    s.add(start <= work_end - duration)
    
    # Busy intervals in minutes
    stephanie_busy = [(600, 630), (960, 990)]
    cheryl_busy = [(600, 630), (690, 720), (810, 840), (990, 1020)]
    bradley_busy = [(570, 600), (630, 690), (810, 840), (870, 900), (930, 1020)]
    steven_busy = [(540, 720), (780, 810), (870, 1020)]
    
    # Add constraints for each participant
    def add_conflicts(busy_intervals):
        for interval in busy_intervals:
            b_start, b_end = interval
            s.add(Or(start + duration <= b_start, start >= b_end))
    
    add_conflicts(stephanie_busy)
    add_conflicts(cheryl_busy)
    add_conflicts(bradley_busy)
    add_conflicts(steven_busy)
    
    # Check for solution
    if s.check() == sat:
        m = s.model()
        start_min = m.evaluate(start).as_long()
        
        # Convert start and end times to HH:MM format
        start_hour = start_min // 60
        start_minute = start_min % 60
        end_min = start_min + duration
        end_hour = end_min // 60
        end_minute = end_min % 60
        
        # Format output
        time_str = f"{start_hour:02d}:{start_minute:02d}:{end_hour:02d}:{end_minute:02d}"
        print(f"Monday {time_str}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()