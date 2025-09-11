from z3 import *

def main():
    # Initialize solver
    s = Solver()
    
    # Meeting duration in minutes (30 minutes)
    meeting_duration = 30
    
    # Total available time in minutes (from 9:00 to 17:00 is 8 hours = 480 minutes)
    total_minutes = 480
    
    # Define start time variable (in minutes from 9:00)
    start = Int('start')
    
    # Constraint: start must be between 0 and total_minutes - meeting_duration
    s.add(start >= 0)
    s.add(start <= total_minutes - meeting_duration)
    
    # Convert busy intervals to minutes from 9:00
    # John: [150, 180], [300, 330]
    john_busy = [(150, 180), (300, 330)]
    # Megan: [180, 210), [300, 360), [390, 420)
    megan_busy = [(180, 210), (300, 360), (390, 420)]
    # Kimberly: [0, 30), [60, 90), [120, 330), [360, 420), [450, 480)
    kimberly_busy = [(0, 30), (60, 90), (120, 330), (360, 420), (450, 480)]
    # Sean: [60, 120), [150, 300), [360, 390)
    sean_busy = [(60, 120), (150, 300), (360, 390)]
    # Lori: [0, 30), [90, 180), [240, 330), [420, 450)
    lori_busy = [(0, 30), (90, 180), (240, 330), (420, 450)]
    
    # Brandon has no meetings, so no constraints
    
    # Function to add no-overlap constraints for a person
    def add_no_overlap(busy_intervals):
        for interval in busy_intervals:
            b_start, b_end = interval
            # Meeting must not overlap with busy interval: 
            # meeting ends before busy starts OR meeting starts after busy ends
            s.add(Or(start + meeting_duration <= b_start, start >= b_end))
    
    # Add constraints for each person
    add_no_overlap(john_busy)
    add_no_overlap(megan_busy)
    add_no_overlap(kimberly_busy)
    add_no_overlap(sean_busy)
    add_no_overlap(lori_busy)
    
    # Check for a solution
    if s.check() == sat:
        m = s.model()
        start_minutes = m.evaluate(start).as_long()
        
        # Convert start minutes to time string
        start_hour = 9 + start_minutes // 60
        start_minute = start_minutes % 60
        end_minutes = start_minutes + meeting_duration
        end_hour = 9 + end_minutes // 60
        end_minute = end_minutes % 60
        
        # Format the time string as HH:MM
        time_str = f"{start_hour:02d}:{start_minute:02d}-{end_hour:02d}:{end_minute:02d}"
        print(f"Monday {time_str}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()