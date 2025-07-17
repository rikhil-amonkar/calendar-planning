from z3 import *

def main():
    # Initialize the solver
    s = Solver()
    
    # Define the start time in minutes from 9:00
    start = Int('start')
    
    # Total working minutes: 9:00 (0 min) to 17:00 (480 min)
    # Meeting duration is 30 minutes, so start must be between 0 and 450 inclusive
    s.add(start >= 0)
    s.add(start <= 450)  # 480 - 30 = 450
    
    # Busy intervals for each participant in minutes (relative to 9:00)
    patrick_busy = [(0, 30), (60, 90), (270, 300), (420, 450)]
    kayla_busy = [(210, 270), (360, 390), (420, 450)]
    carl_busy = [(90, 120), (180, 210), (240, 270), (330, 480)]
    christian_busy = [(0, 210), (240, 300), (330, 480)]
    
    # Combine all busy intervals
    all_busy = patrick_busy + kayla_busy + carl_busy + christian_busy
    
    # For each busy interval, add constraint: meeting must not overlap
    for a, b in all_busy:
        # The meeting is [start, start+30]
        # Non-overlap: either meeting ends before a or starts after b
        s.add(Or(start + 30 <= a, start >= b))
    
    # Check if there's a solution
    if s.check() == sat:
        m = s.model()
        start_min = m.eval(start).as_long()
        
        # Convert minutes back to time string
        hours = 9 + start_min // 60
        minutes = start_min % 60
        start_time = f"{hours:02d}:{minutes:02d}"
        
        # Calculate end time (start + 30 minutes)
        end_min = start_min + 30
        end_hours = 9 + end_min // 60
        end_minutes = end_min % 60
        end_time = f"{end_hours:02d}:{end_minutes:02d}"
        
        # Output in the required format
        print("SOLUTION:")
        print("Day: Monday")
        print(f"Start Time: {start_time}")
        print(f"End Time: {end_time}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()