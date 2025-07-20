from z3 import *

def main():
    # Initialize solver
    s = Solver()
    
    # Define variables
    day = Int('day')
    start_minutes = Int('start_minutes')
    
    # Constraints for day and start time
    s.add(Or(day == 0, day == 1, day == 3))
    s.add(start_minutes >= 0)
    s.add(start_minutes <= 420)  # 420 minutes ensures the meeting ends by 17:00 (420+60=480 minutes = 17:00)
    
    # Define busy intervals in minutes (relative to 9:00)
    laura_busy = {
        0: [(90, 120), (150, 180), (330, 390), (420, 480)],   # Monday
        1: [(30, 60), (120, 150), (240, 270), (330, 360), (420, 480)],  # Tuesday
        3: [(90, 120), (180, 270), (360, 390), (420, 450)]    # Thursday
    }
    
    philip_busy = {
        0: [(0, 480)],   # Monday (entire day)
        1: [(0, 120), (150, 180), (240, 270), (300, 330), (360, 450)],  # Tuesday
        3: [(0, 90), (120, 210), (240, 480)]   # Thursday
    }
    
    # Add constraints for Laura's busy intervals
    for d in [0, 1, 3]:
        for (s_start, s_end) in laura_busy[d]:
            s.add(Implies(day == d, Or(start_minutes + 60 <= s_start, start_minutes >= s_end)))
    
    # Add constraints for Philip's busy intervals
    for d in [0, 1, 3]:
        for (s_start, s_end) in philip_busy[d]:
            s.add(Implies(day == d, Or(start_minutes + 60 <= s_start, start_minutes >= s_end)))
    
    # Check for a solution
    if s.check() == sat:
        m = s.model()
        d_val = m[day].as_long()
        start_val = m[start_minutes].as_long()
        
        # Map day value to day name
        day_map = {0: "Monday", 1: "Tuesday", 3: "Thursday"}
        day_name = day_map[d_val]
        
        # Calculate start time in hours and minutes
        start_hour = 9 + start_val // 60
        start_min = start_val % 60
        start_time = f"{start_hour}:{start_min:02d}"
        
        # Calculate end time
        end_val = start_val + 60
        end_hour = 9 + end_val // 60
        end_min = end_val % 60
        end_time = f"{end_hour}:{end_min:02d}"
        
        # Print the solution
        print(f"Day: {day_name}")
        print(f"Start: {start_time}")
        print(f"End: {end_time}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()