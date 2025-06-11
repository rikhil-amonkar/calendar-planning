from z3 import *

def main():
    # Initialize solver
    s = Solver()
    
    # Define start time in minutes from 9:00 (0 minutes = 9:00)
    start = Int('start')
    duration = 60
    end = start + duration
    
    # Working hours: 9:00 (0 min) to 17:00 (480 min)
    s.add(start >= 0)
    s.add(end <= 480)
    
    # Danielle's meetings: converted to minutes
    danielle_meetings = [
        (0, 60),    # 9:00-10:00
        (90, 120),   # 10:30-11:00
        (330, 360),  # 14:30-15:00
        (390, 420),  # 15:30-16:00
        (450, 480)   # 16:30-17:00
    ]
    
    # Bruce's meetings
    bruce_meetings = [
        (120, 150), # 11:00-11:30
        (210, 240), # 12:30-13:00
        (300, 330), # 14:00-14:30
        (390, 420)  # 15:30-16:00
    ]
    
    # Eric's meetings
    eric_meetings = [
        (0, 30),    # 9:00-9:30
        (60, 120),  # 10:00-11:00
        (150, 240), # 11:30-13:00
        (330, 390)  # 14:30-15:30
    ]
    
    # Function to add non-overlap constraints for each person's meetings
    def add_non_overlap(meetings):
        for meet_start, meet_end in meetings:
            s.add(Or(end <= meet_start, start >= meet_end))
    
    # Add constraints for each participant
    add_non_overlap(danielle_meetings)
    add_non_overlap(bruce_meetings)
    add_non_overlap(eric_meetings)
    
    # Check for a solution
    if s.check() == sat:
        m = s.model()
        start_min = m[start].as_long()
        # Convert minutes back to time string
        hours = 9 + start_min // 60
        minutes = start_min % 60
        start_time = f"{hours:02d}:{minutes:02d}"
        end_min = start_min + 60
        end_hours = 9 + end_min // 60
        end_minutes = end_min % 60
        end_time = f"{end_hours:02d}:{end_minutes:02d}"
        print(f"Monday {start_time} to {end_time}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()