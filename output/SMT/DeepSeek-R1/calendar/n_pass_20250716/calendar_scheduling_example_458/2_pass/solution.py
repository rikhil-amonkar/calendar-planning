from z3 import Solver, Int, Or, And, sat

def main():
    s = Solver()
    start = Int('start')
    
    # Meeting duration in minutes
    duration = 30
    
    # Total working minutes (9:00 to 17:00 is 480 minutes)
    max_start = 480 - duration  # 450 minutes (17:00 - 30 minutes)
    
    # Constraint: meeting must be within working hours
    s.add(start >= 0, start <= max_start)
    
    # Wayne's preference: avoid before 14:00 (14:00 is 300 minutes from 9:00)
    s.add(start >= 300)
    
    # Busy intervals for each participant (in minutes from 9:00)
    busy_intervals = [
        # Melissa
        (60, 120), (210, 300), (360, 390),
        # Gregory
        (210, 240), (390, 420),
        # Victoria
        (0, 30), (90, 150), (240, 300), (330, 360), (390, 450),
        # Thomas
        (60, 180), (210, 240), (330, 420),
        # Jennifer
        (0, 30), (60, 90), (120, 240), (270, 330), (360, 390), (420, 450)
    ]
    
    # Add constraints for each busy interval
    for (busy_start, busy_end) in busy_intervals:
        # The meeting must not overlap: either entirely before or entirely after the busy interval
        s.add(Or(
            start + duration <= busy_start,
            start >= busy_end
        ))
    
    # Check for a solution
    if s.check() == sat:
        model = s.model()
        start_minutes = model[start].as_long()
        # Convert start_minutes to time string
        hours = 9 + start_minutes // 60
        minutes = start_minutes % 60
        start_time = f"{hours:02d}:{minutes:02d}"
        end_minutes = start_minutes + duration
        end_hours = 9 + end_minutes // 60
        end_minutes = end_minutes % 60
        end_time = f"{end_hours:02d}:{end_minutes:02d}"
        print(f"Monday {start_time} to {end_time}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()