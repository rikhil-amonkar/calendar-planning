from z3 import *

def main():
    s = Solver()
    start = Int('start')
    
    # Work hours: 9:00 (540) to 17:00 (1020). Meeting duration 30 min => start in [540, 990]
    s.add(start >= 540)
    s.add(start <= 990)
    
    # Margaret's constraint: not before 14:30 (870 minutes)
    s.add(start >= 870)
    
    # Start time must be on a 30-minute boundary
    s.add(start % 30 == 0)
    
    # Busy intervals for each participant (start, end) in minutes
    busy_times = {
        'Shirley': [(630, 660), (720, 750)],
        'Jacob': [(540, 570), (600, 630), (660, 690), (750, 810), (870, 900)],
        'Stephen': [(690, 720), (750, 780)],
        'Margaret': [(540, 570), (630, 750), (780, 810), (900, 930), (990, 1020)],
        'Mason': [(540, 600), (630, 660), (690, 750), (780, 810), (840, 870), (990, 1020)]
    }
    
    # Add constraints for each busy interval
    for intervals in busy_times.values():
        for s_busy, e_busy in intervals:
            s.add(Or(start + 30 <= s_busy, start >= e_busy))
    
    if s.check() == sat:
        m = s.model()
        start_val = m[start].as_long()
        hours = start_val // 60
        minutes = start_val % 60
        start_time = f"{hours}:{minutes:02d}"
        end_val = start_val + 30
        end_hours = end_val // 60
        end_minutes = end_val % 60
        end_time = f"{end_hours}:{end_minutes:02d}"
        print(f"Monday {start_time} to {end_time}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()