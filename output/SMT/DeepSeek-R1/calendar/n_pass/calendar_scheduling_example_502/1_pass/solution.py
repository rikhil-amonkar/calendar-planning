from z3 import *

def main():
    # Initialize solver
    s = Solver()
    
    # Define start time in minutes (from 00:00)
    start = Int('start')
    
    # Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
    s.add(start >= 540)          # Start no earlier than 9:00
    s.add(start + 30 <= 1020)    # End no later than 17:00
    
    # Jack's busy intervals (each as (start_minute, end_minute))
    busy_jack = [
        (9*60 + 30, 10*60 + 30),  # 9:30-10:30
        (11*60, 11*60 + 30),       # 11:00-11:30
        (12*60 + 30, 13*60),       # 12:30-13:00
        (14*60, 14*60 + 30),       # 14:00-14:30
        (16*60, 16*60 + 30)        # 16:00-16:30
    ]
    
    # Charlotte's busy intervals
    busy_charlotte = [
        (9*60 + 30, 10*60),        # 9:30-10:00
        (10*60 + 30, 12*60),       # 10:30-12:00
        (12*60 + 30, 13*60 + 30),  # 12:30-13:30
        (14*60, 16*60)             # 14:00-16:00
    ]
    
    # Add constraints for Jack's busy intervals
    for (s_busy, e_busy) in busy_jack:
        s.add(Or(start + 30 <= s_busy, start >= e_busy))
    
    # Add constraints for Charlotte's busy intervals
    for (s_busy, e_busy) in busy_charlotte:
        s.add(Or(start + 30 <= s_busy, start >= e_busy))
    
    # Preference: meeting should end by 12:30 (750 minutes)
    s.push()
    s.add(start + 30 <= 750)
    
    # Check if solution exists with preference
    if s.check() == sat:
        model = s.model()
        start_val = model[start].as_long()
    else:
        s.pop()  # Remove preference constraint
        # Check for any feasible solution
        if s.check() == sat:
            model = s.model()
            start_val = model[start].as_long()
        else:
            # According to the problem, a solution exists, so this should not happen
            print("No solution found, but the problem guarantees one exists.")
            return
    
    # Calculate end time
    end_val = start_val + 30
    
    # Convert start and end times to HH:MM format
    def minutes_to_time(minutes):
        hours = minutes // 60
        mins = minutes % 60
        return f"{hours:02d}:{mins:02d}"
    
    start_str = minutes_to_time(start_val)
    end_str = minutes_to_time(end_val)
    
    # Output the solution
    print("SOLUTION:")
    print("Day: Monday")
    print(f"Start Time: {start_str}")
    print(f"End Time: {end_str}")

if __name__ == "__main__":
    main()