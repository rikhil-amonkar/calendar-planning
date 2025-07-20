from z3 import *

def main():
    s = Solver()
    
    # Start time in minutes from 9:00 (0 minutes = 9:00)
    S = Int('S')
    s.add(S >= 0, S <= 450)  # Meeting must start between 9:00 and 16:30
    
    # Jose's constraint: meeting must end by 15:30 (390 minutes from 9:00)
    s.add(S + 30 <= 390)
    
    # Busy intervals for each participant (start and end in minutes from 9:00)
    jose_busy = [(120, 150), (210, 240)]
    keith_busy = [(300, 330), (360, 390)]
    logan_busy = [(0, 60), (180, 210)]
    megan_busy = [(0, 90), (120, 180), (240, 270), (330, 450)]
    gary_busy = [(0, 30), (60, 90), (150, 240), (270, 300), (330, 450)]
    bobby_busy = [(120, 150), (180, 210), (240, 420)]
    
    # Combine all busy intervals
    all_busy = jose_busy + keith_busy + logan_busy + megan_busy + gary_busy + bobby_busy
    
    # Add constraints: meeting [S, S+30] must not overlap with any busy interval [b_start, b_end]
    for (b_start, b_end) in all_busy:
        s.add(Or(S + 30 <= b_start, S >= b_end))
    
    # Check for a solution
    if s.check() == sat:
        model = s.model()
        start_minutes = model.eval(S).as_long()
        
        # Convert start_minutes back to time string (from minutes since 9:00)
        total_minutes = start_minutes
        hours = total_minutes // 60
        minutes = total_minutes % 60
        start_hour = 9 + hours
        start_str = f"{start_hour:02d}:{minutes:02d}"
        
        # Calculate end time (start_minutes + 30)
        end_minutes = start_minutes + 30
        end_hours = end_minutes // 60
        end_mins = end_minutes % 60
        end_hour = 9 + end_hours
        end_str = f"{end_hour:02d}:{end_mins:02d}"
        
        # Print the solution in the required format
        print("SOLUTION:")
        print("Day: Monday")
        print(f"Start Time: {start_str}")
        print(f"End Time: {end_str}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()