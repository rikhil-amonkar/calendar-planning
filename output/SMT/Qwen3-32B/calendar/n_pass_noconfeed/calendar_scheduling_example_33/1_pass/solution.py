from z3 import *

def main():
    s = Solver()
    start = Int('start')
    
    # Work hours from 9:00 (540) to 17:00 (1020)
    s.add(start >= 540)
    s.add(start + 30 <= 1020)
    
    # Bobby's preference: meeting ends by 15:00 (900 minutes)
    s.add(start + 30 <= 900)
    
    # Busy intervals in minutes since midnight
    lisa_busy = [(540, 600), (630, 690), (750, 780), (960, 990)]
    bobby_busy = [(540, 570), (600, 630), (690, 720), (900, 930)]
    randy_busy = [(570, 600), (630, 660), (690, 750), (780, 810), (870, 930), (960, 990)]
    
    for busy_intervals in [lisa_busy, bobby_busy, randy_busy]:
        for busy_start, busy_end in busy_intervals:
            # Meeting does not overlap with busy interval
            s.add(Or(start + 30 <= busy_start, start >= busy_end))
    
    if s.check() == sat:
        model = s.model()
        start_val = model[start].as_long()
        end_val = start_val + 30
        
        def to_time(m):
            hours = m // 60
            minutes = m % 60
            return f"{hours:02d}:{minutes:02d}"
        
        start_time = to_time(start_val)
        end_time = to_time(end_val)
        print(f"Monday {start_time}:{end_time}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()