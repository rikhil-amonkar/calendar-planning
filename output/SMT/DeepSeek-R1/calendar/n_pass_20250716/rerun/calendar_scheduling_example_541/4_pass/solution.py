from z3 import Solver, Real, Or

def main():
    s = Solver()
    start = Real('start')
    
    # Convert work hours to minutes (9:00 = 0, 17:00 = 480)
    work_start = 0
    work_end = 480
    meeting_duration = 60
    
    # Meeting must be within work hours and have enough time
    s.add(start >= work_start)
    s.add(start <= work_end - meeting_duration)
    
    # Blocked times in minutes from 9:00
    kayla_blocks = [
        (60, 90),    # 10:00-10:30
        (330, 420)    # 14:30-16:00
    ]
    rebecca_blocks = [
        (0, 240),     # 9:00-13:00
        (270, 360),   # 13:30-15:00
        (390, 420)    # 15:30-16:00
    ]
    
    # Add constraints to avoid blocked times
    for a, b in kayla_blocks:
        s.add(Or(start + meeting_duration <= a, start >= b))
    
    for a, b in rebecca_blocks:
        s.add(Or(start + meeting_duration <= a, start >= b))
    
    # Solve and format output
    if s.check() == 'sat':
        m = s.model()
        start_val = m[start]
        # Convert fractional solution to integer minutes
        start_min = int(float(str(m[start])))
        
        # Calculate start time (HH:MM)
        start_hr = 9 + start_min // 60
        start_min %= 60
        # Calculate end time (HH:MM)
        end_min_total = start_min + 60
        end_hr = 9 + (start_min + 60) // 60
        end_min = end_min_total % 60
        
        print(f"Monday {start_hr:02d}:{start_min:02d} to {end_hr:02d}:{end_min:02d}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()