from z3 import *

def main():
    # Define busy times in minutes from 9:00 (start of day)
    busy_times = {
        'Megan': [(0, 30), (60, 120), (180, 210)],
        'Christine': [(0, 30), (150, 180), (240, 300), (390, 450)],
        'Gabriel': [],
        'Sara': [(150, 180), (330, 360)],
        'Bruce': [(30, 60), (90, 180), (210, 300), (330, 360), (390, 450)],
        'Kathryn': [(60, 390), (420, 450)],
        'Billy': [(0, 30), (120, 150), (180, 300), (330, 390)]
    }
    
    # Initialize Z3 solver and variable for meeting start time (in minutes)
    s = Solver()
    start = Int('start')
    
    # Meeting must be within 9:00 to 17:00 (start between 0 and 450 minutes inclusive)
    s.add(start >= 0)
    s.add(start <= 450)
    
    # Add constraints for each participant
    for person, intervals in busy_times.items():
        for interval in intervals:
            s_start, s_end = interval
            # Ensure meeting does not overlap: either ends before interval starts or starts after interval ends
            s.add(Or(start + 30 <= s_start, start >= s_end))
    
    # Check for a solution
    if s.check() == sat:
        model = s.model()
        start_val = model[start].as_long()
        
        # Convert start time back to HH:MM format
        total_minutes = 9 * 60 + start_val
        hours = total_minutes // 60
        minutes = total_minutes % 60
        start_time = f"{hours:02d}:{minutes:02d}"
        
        # Calculate end time (30 minutes later)
        end_minutes = start_val + 30
        total_end_minutes = 9 * 60 + end_minutes
        end_hours = total_end_minutes // 60
        end_minutes = total_end_minutes % 60
        end_time = f"{end_hours:02d}:{end_minutes:02d}"
        
        print(f"Monday, {start_time} to {end_time}")
    else:
        print("No suitable time found")

if __name__ == "__main__":
    main()