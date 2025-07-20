from z3 import Solver, Int, Or, And

def main():
    s = Solver()
    start = Int('start')
    
    # Total work minutes: 9:00 to 17:00 = 480 minutes
    work_start = 0
    work_end = 480
    meeting_duration = 60
    
    # Meeting must be within work hours and have enough time
    s.add(start >= work_start)
    s.add(start <= work_end - meeting_duration)
    
    # Kayla's blocked intervals (in minutes from 9:00)
    kayla_blocks = [
        (60, 90),   # 10:00-10:30
        (330, 420)   # 14:30-16:00
    ]
    # Rebecca's blocked intervals
    rebecca_blocks = [
        (0, 240),    # 9:00-13:00
        (270, 360),  # 13:30-15:00
        (390, 420)   # 15:30-16:00
    ]
    
    # Function to add no-overlap constraints
    def add_no_overlap(blocks):
        for a, b in blocks:
            # Meeting must be completely before or after the block
            s.add(Or(
                start + meeting_duration <= a,  # Ends before block starts
                start >= b                      # Starts after block ends
            ))
    
    add_no_overlap(kayla_blocks)
    add_no_overlap(rebecca_blocks)
    
    # Check for solution
    if s.check() == 'sat':
        model = s.model()
        start_min = model[start].as_long()
        
        # Convert to time format
        start_hour = 9 + start_min // 60
        start_min %= 60
        end_min = start_min + meeting_duration
        end_hour = 9 + (model[start].as_long() + meeting_duration) // 60
        end_min %= 60
        
        # Format and print result
        print(f"Monday {start_hour:02d}:{start_min:02d} to {end_hour:02d}:{end_min:02d}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()