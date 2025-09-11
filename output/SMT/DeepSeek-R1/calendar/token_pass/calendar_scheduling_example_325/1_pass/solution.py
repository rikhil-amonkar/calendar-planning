from z3 import Int, Solver, And, Or, Not

def main():
    # Initialize solver
    s = Solver()
    
    # Define start time in minutes from 9:00 (0 minutes) to 17:00 (480 minutes)
    start = Int('start')
    meeting_duration = 30
    end = start + meeting_duration
    
    # Work hours: 9:00 to 17:00 (0 to 480 minutes)
    s.add(start >= 0)
    s.add(end <= 480)
    
    # Jose's constraint: meeting must end by 15:30 (390 minutes from 9:00)
    s.add(end <= 390)
    
    # Convert busy times to minutes from 9:00
    busy_intervals = {
        'Jose': [(120, 150), (210, 240)],
        'Keith': [(300, 330), (360, 390)],
        'Logan': [(0, 60), (180, 210), (360, 390)],
        'Megan': [(0, 90), (120, 180), (240, 270), (330, 450)],
        'Gary': [(0, 30), (60, 90), (150, 240), (270, 300), (330, 450)],
        'Bobby': [(120, 150), (180, 210), (240, 420)]
    }
    
    # Add constraints for each person's busy intervals
    for person, intervals in busy_intervals.items():
        for interval in intervals:
            busystart, busyend = interval
            # Meeting must not overlap with busy interval
            s.add(Or(
                end <= busystart,
                start >= busyend
            ))
    
    # Check for solution
    if s.check() == sat:
        m = s.model()
        start_min = m.evaluate(start).as_long()
        
        # Convert start and end minutes to time strings
        start_hour = 9 + start_min // 60
        start_minute = start_min % 60
        end_min = start_min + meeting_duration
        end_hour = 9 + end_min // 60
        end_minute = end_min % 60
        
        # Format output
        print(f"{start_hour:02d}:{start_minute:02d}:{end_hour:02d}:{end_minute:02d}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()