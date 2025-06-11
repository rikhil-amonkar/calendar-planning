from z3 import *

def main():
    # Initialize solver
    s = Solver()
    
    # Meeting duration in minutes
    duration = 30
    
    # Total available time in minutes (from 9:00 to 17:00)
    total_minutes = 8 * 60  # 480 minutes
    max_start = total_minutes - duration  # 450 minutes (17:00 - 30 minutes)
    
    # Start time variable (in minutes from 9:00)
    S = Int('S')
    s.add(S >= 0, S <= max_start)
    
    # Roger's constraint: meeting starts at or after 12:30 (210 minutes from 9:00)
    s.add(S >= 210)
    
    # Busy intervals for each participant (in minutes from 9:00)
    busy_intervals = {
        # Daniel: no meetings
        'Daniel': [],
        # Kathleen: 14:30 to 15:30 -> 330 to 390
        'Kathleen': [(330, 390)],
        # Carolyn: 12:00-12:30 -> 180 to 210; 13:00-13:30 -> 240 to 270
        'Carolyn': [(180, 210), (240, 270)],
        # Roger: free entire day (only preference constraint already added)
        'Roger': [],
        # Cheryl: 9:00-9:30 -> 0-30; 10:00-11:30 -> 60-150; 12:30-13:30 -> 210-270; 14:00-17:00 -> 300-480
        'Cheryl': [(0, 30), (60, 150), (210, 270), (300, 480)],
        # Virginia: 9:30-11:30 -> 30-150; 12:00-12:30 -> 180-210; 13:00-13:30 -> 240-270; 14:30-15:30 -> 330-390; 16:00-17:00 -> 420-480
        'Virginia': [(30, 150), (180, 210), (240, 270), (330, 390), (420, 480)],
        # Angela: 9:30-10:00 -> 30-60; 10:30-11:30 -> 90-150; 12:00-12:30 -> 180-210; 13:00-13:30 -> 240-270; 14:00-16:30 -> 300-450
        'Angela': [(30, 60), (90, 150), (180, 210), (240, 270), (300, 450)]
    }
    
    # Add constraints for each participant's busy intervals
    for participant, intervals in busy_intervals.items():
        for start, end in intervals:
            # Meeting must not overlap: either entirely before or entirely after the busy interval
            s.add(Or(S >= end, S + duration <= start))
    
    # Check for a solution
    if s.check() == sat:
        model = s.model()
        start_minutes = model[S].as_long()
        
        # Convert start_minutes back to time string
        hours = 9 + start_minutes // 60
        minutes = start_minutes % 60
        start_time = f"{hours:02d}:{minutes:02d}"
        
        # Calculate end time
        end_minutes = start_minutes + duration
        end_hours = 9 + end_minutes // 60
        end_minutes = end_minutes % 60
        end_time = f"{end_hours:02d}:{end_minutes:02d}"
        
        print(f"Monday, {start_time}, {end_time}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()