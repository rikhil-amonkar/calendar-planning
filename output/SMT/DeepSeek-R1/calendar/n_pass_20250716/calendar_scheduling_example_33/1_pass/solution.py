from z3 import *

def main():
    # Meeting duration in minutes
    duration = 30
    # Total available time in minutes (9:00 to 17:00)
    total_minutes = 480

    # Busy intervals for each participant in minutes (from 9:00)
    lisa_busy = [(0, 60), (90, 150), (210, 240), (420, 450)]
    bobby_busy = [(0, 30), (60, 90), (150, 180), (360, 390)]
    randy_busy = [(30, 60), (90, 120), (150, 210), (240, 270), (330, 390), (420, 450)]
    
    # Create a Z3 integer variable for the start time
    s = Int('s')
    
    # Constraints: meeting must be within work hours (9:00 to 17:00)
    constraints = [s >= 0, s + duration <= total_minutes]
    
    # Add constraints for each participant's busy intervals
    # For each busy interval (start, end), the meeting must either end before the interval starts or start after the interval ends.
    def add_busy_constraints(busy_intervals):
        for (start_int, end_int) in busy_intervals:
            constraints.append(Or(s + duration <= start_int, s >= end_int))
    
    add_busy_constraints(lisa_busy)
    add_busy_constraints(bobby_busy)
    add_busy_constraints(randy_busy)
    
    # Use an optimizer to find the earliest start time
    opt = Optimize()
    opt.add(constraints)
    opt.minimize(s)
    
    if opt.check() == sat:
        m = opt.model()
        start_minutes = m.eval(s).as_long()
        
        # Convert start_minutes back to time string
        hours = 9 + start_minutes // 60
        minutes = start_minutes % 60
        start_time = f"{hours}:{minutes:02d}"
        
        end_minutes = start_minutes + duration
        hours_end = 9 + end_minutes // 60
        minutes_end = end_minutes % 60
        end_time = f"{hours_end}:{minutes_end:02d}"
        
        print(f"Monday {start_time} to {end_time}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()