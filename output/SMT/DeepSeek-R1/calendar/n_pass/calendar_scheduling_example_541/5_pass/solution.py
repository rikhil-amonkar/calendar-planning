from z3 import Solver, Int, Or

def main():
    s = Solver()
    start = Int('start')
    meeting_duration = 60
    total_work_minutes = 480  # 9:00 to 17:00 (8 hours)
    
    # Meeting must be within work hours
    s.add(start >= 0)
    s.add(start <= total_work_minutes - meeting_duration)  # 420 minutes max
    
    # Blocked times (start inclusive, end exclusive)
    kayla_blocks = [
        (60, 90),    # 10:00-10:30
        (330, 420)   # 14:30-16:00
    ]
    rebecca_blocks = [
        (0, 240),    # 9:00-13:00
        (270, 360),  # 13:30-15:00
        (390, 420)   # 15:30-16:00
    ]
    
    # Combine all blocked time intervals
    all_blocks = kayla_blocks + rebecca_blocks
    
    # Add constraints: meeting must not overlap with any blocked period
    for block_start, block_end in all_blocks:
        # Meeting must end before block starts OR start after block ends
        s.add(Or(
            start + meeting_duration <= block_start,
            start >= block_end
        ))
    
    # Check for solution
    if s.check() == 'sat':
        m = s.model()
        start_minutes = m[start].as_long()
        
        # Calculate start time (from 9:00 base)
        start_hour = 9 + start_minutes // 60
        start_minute = start_minutes % 60
        
        # Calculate end time
        end_minutes = start_minutes + meeting_duration
        end_hour = 9 + end_minutes // 60
        end_minute = end_minutes % 60
        
        print(f"Monday {start_hour:02d}:{start_minute:02d} to {end_hour:02d}:{end_minute:02d}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()