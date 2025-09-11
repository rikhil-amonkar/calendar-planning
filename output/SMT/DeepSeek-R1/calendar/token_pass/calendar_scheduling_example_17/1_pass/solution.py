from z3 import Int, Solver, And, Or, Not

def main():
    # Initialize solver
    s = Solver()
    
    # Define start time in minutes from 9:00 (0 minutes = 9:00)
    start = Int('start')
    duration = 30
    end = start + duration
    
    # Work hours: 9:00 to 17:00 (0 to 480 minutes)
    s.add(start >= 0)
    s.add(end <= 480)
    
    # Margaret's blocked intervals (in minutes from 9:00)
    margaret_busy = [
        (0, 60),    # 9:00-10:00
        (90, 120),  # 10:30-11:00
        (150, 180), # 11:30-12:00
        (240, 270), # 13:00-13:30
        (360, 390)  # 15:00-15:30
    ]
    
    # Donna's blocked intervals
    donna_busy = [
        (330, 360), # 14:30-15:00
        (420, 450)  # 16:00-16:30
    ]
    
    # Helen's meetings and preference (no meeting after 13:30)
    helen_busy = [
        (0, 30),    # 9:00-9:30
        (60, 150),  # 10:00-11:30
        (240, 300), # 13:00-14:00
        (330, 360), # 14:30-15:00
        (390, 480)  # 15:30-17:00
    ]
    # Helen's preference: meeting must end by 13:30 (270 minutes)
    s.add(end <= 270)
    
    # Function to add no-overlap constraints
    def add_no_overlap(busy_intervals):
        for busystart, busyend in busy_intervals:
            s.add(Or(start >= busyend, end <= busystart))
    
    # Add constraints for each participant
    add_no_overlap(margaret_busy)
    add_no_overlap(donna_busy)
    add_no_overlap(helen_busy)
    
    # Check for a solution
    if s.check() == sat:
        m = s.model()
        start_min = m.evaluate(start).as_long()
        
        # Convert start and end times to HH:MM format
        start_hour = 9 + start_min // 60
        start_minute = start_min % 60
        end_min = start_min + duration
        end_hour = 9 + end_min // 60
        end_minute = end_min % 60
        
        # Format the output
        print(f"Monday {start_hour:02d}:{start_minute:02d}:{end_hour:02d}:{end_minute:02d}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()