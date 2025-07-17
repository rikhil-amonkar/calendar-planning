from z3 import *

def main():
    # Create the solver and variable for start time in minutes from 9:00
    s = Solver()
    t = Int('t')
    
    # Global constraints: meeting within work hours and Helen's preference (end by 13:30)
    s.add(t >= 0)                # Start at or after 9:00
    s.add(t + 30 <= 270)          # End by 13:30 (270 minutes from 9:00)
    
    # Margaret's blocked intervals in minutes
    margaret_blocks = [
        (0, 60),    # 9:00-10:00
        (90, 120),  # 10:30-11:00
        (150, 180), # 11:30-12:00
        (240, 270), # 13:00-13:30
        (360, 390)  # 15:00-15:30
    ]
    
    # Donna's blocked intervals
    donna_blocks = [
        (330, 360), # 14:30-15:00
        (420, 450)  # 16:00-16:30
    ]
    
    # Helen's blocked intervals
    helen_blocks = [
        (0, 30),    # 9:00-9:30
        (60, 150),  # 10:00-11:30
        (240, 300), # 13:00-14:00
        (330, 360), # 14:30-15:00
        (390, 480)  # 15:30-17:00
    ]
    
    # Add constraints for Margaret's blocks
    for (a, b) in margaret_blocks:
        s.add(Or(t + 30 <= a, t >= b))
    
    # Add constraints for Donna's blocks
    for (a, b) in donna_blocks:
        s.add(Or(t + 30 <= a, t >= b))
    
    # Add constraints for Helen's blocks
    for (a, b) in helen_blocks:
        s.add(Or(t + 30 <= a, t >= b))
    
    # Check for a solution
    if s.check() == sat:
        model = s.model()
        t_val = model[t].as_long()
        
        # Convert start time from minutes to HH:MM format
        start_hour = 9 + t_val // 60
        start_min = t_val % 60
        start_str = f"{start_hour}:{start_min:02d}"
        
        # Calculate end time (start time + 30 minutes)
        end_val = t_val + 30
        end_hour = 9 + end_val // 60
        end_min = end_val % 60
        end_str = f"{end_hour}:{end_min:02d}"
        
        # Output the meeting time
        print(f"Monday {start_str} to {end_str}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()