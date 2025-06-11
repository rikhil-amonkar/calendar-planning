from z3 import Solver, Int, Or, sat

def main():
    s = Solver()
    # Start time in minutes after 9:00
    S = Int('S')
    
    # Meeting must be within 9:00 (0 min) to 17:00 (480 min), duration 60 min -> S in [0, 420]
    s.add(S >= 0)
    s.add(S <= 420)
    
    # James' busy intervals in minutes (exclusive end)
    # 11:30-12:00 -> [150, 180)
    # 14:30-15:00 -> [330, 360)
    s.add(Or(S + 60 <= 150, S >= 180))
    s.add(Or(S + 60 <= 330, S >= 360))
    
    # John's busy intervals in minutes (exclusive end)
    # 9:30-11:00 -> [30, 120)
    # 11:30-12:00 -> [150, 180)
    # 12:30-13:30 -> [210, 270)
    # 14:30-16:30 -> [330, 450)
    s.add(Or(S + 60 <= 30, S >= 120))
    s.add(Or(S + 60 <= 150, S >= 180))
    s.add(Or(S + 60 <= 210, S >= 270))
    s.add(Or(S + 60 <= 330, S >= 450))
    
    # Check for a solution
    if s.check() == sat:
        model = s.model()
        start_minutes = model[S].as_long()
        
        # Convert start_minutes to hours and minutes
        hours = start_minutes // 60
        minutes = start_minutes % 60
        start_time = f"{9 + hours}:{minutes:02d}"
        
        # Calculate end time (start + 60 minutes)
        end_minutes = start_minutes + 60
        end_hours = end_minutes // 60
        end_min = end_minutes % 60
        end_time = f"{9 + end_hours}:{end_min:02d}"
        
        print("Monday", start_time, end_time)
    else:
        print("No solution found")

if __name__ == "__main__":
    main()