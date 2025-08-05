from z3 import Int, Optimize, Or, sat

def main():
    # Convert busy times to minutes from 9:00
    Lisa_busy = [(0, 30), (90, 120), (300, 420)]
    Anthony_busy = [(0, 30), (120, 150), (210, 270), (300, 360), (390, 420), (450, 480)]
    meeting_duration = 30
    max_start = 480 - meeting_duration  # 450 minutes

    # Initialize Z3 solver and variable
    s = Optimize()
    start = Int('start')
    s.add(start >= 0)
    s.add(start <= max_start)

    # Add constraints for Lisa's busy intervals
    for (s1, e1) in Lisa_busy:
        s.add(Or(start + meeting_duration <= s1, start >= e1))

    # Add constraints for Anthony's busy intervals
    for (s1, e1) in Anthony_busy:
        s.add(Or(start + meeting_duration <= s1, start >= e1))

    # Minimize start time
    s.minimize(start)

    if s.check() == sat:
        m = s.model()
        start_val = m.eval(start).as_long()
        
        # Convert minutes back to time
        total_minutes = start_val
        hour = 9 + total_minutes // 60
        minute = total_minutes % 60
        start_time = f"{hour:02d}:{minute:02d}"
        
        end_minutes = start_val + meeting_duration
        end_hour = 9 + end_minutes // 60
        end_minute = end_minutes % 60
        end_time = f"{end_hour:02d}:{end_minute:02d}"
        
        # Output the solution
        print("SOLUTION:")
        print("Day: Monday")
        print(f"Start Time: {start_time}")
        print(f"End Time: {end_time}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()