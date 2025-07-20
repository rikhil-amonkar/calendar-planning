from z3 import *

def main():
    # Hardcoded busy blocks in minutes from 9:00
    ronald_busy = {
        "Monday": [(90, 120), (180, 210), (390, 420)],
        "Tuesday": [(0, 30), (180, 210), (390, 450)],
        "Wednesday": [(30, 90), (120, 180), (210, 240), (270, 300), (450, 480)]
    }
    
    amber_busy = {
        "Monday": [(0, 30), (60, 90), (150, 180), (210, 300), (330, 360), (390, 480)],
        "Tuesday": [(0, 30), (60, 150), (180, 210), (270, 390), (450, 480)],
        "Wednesday": [(0, 30), (60, 90), (120, 270), (360, 390)]
    }
    
    days_str = ["Monday", "Tuesday", "Wednesday"]
    
    # Create Z3 variables
    day_var = Int('day')
    start_var = Int('start')
    
    # Create solver
    s = Optimize()
    
    # Day must be 0, 1, or 2
    s.add(day_var >= 0, day_var <= 2)
    # Start time must be between 0 and 450 (inclusive) to fit the meeting
    s.add(start_var >= 0, start_var <= 450)
    
    # For each day, add constraints that the meeting does not conflict with any busy block
    for d in range(3):
        day_name = days_str[d]
        # Constraints for Ronald's busy blocks on this day
        ronald_constraints = []
        for block in ronald_busy[day_name]:
            s_start, s_end = block
            # Non-overlap: meeting ends before block starts OR meeting starts after block ends
            ronald_constraints.append(Or(start_var + 30 <= s_start, start_var >= s_end))
        # Constraints for Amber's busy blocks on this day
        amber_constraints = []
        for block in amber_busy[day_name]:
            s_start, s_end = block
            amber_constraints.append(Or(start_var + 30 <= s_start, start_var >= s_end))
        
        # If the meeting is on this day, then both participants must be free
        s.add(Implies(day_var == d, And(And(ronald_constraints), And(amber_constraints)))
    
    # Minimize: earliest day and then earliest start time
    s.minimize(day_var * 1000 + start_var)
    
    # Check for solution
    if s.check() == sat:
        m = s.model()
        d_val = m[day_var].as_long()
        start_val = m[start_var].as_long()
        
        day_name = days_str[d_val]
        # Convert start minutes to time
        total_minutes = start_val
        hours = 9 + total_minutes // 60
        minutes = total_minutes % 60
        start_time = f"{hours:02d}:{minutes:02d}"
        
        # Calculate end time (start + 30 minutes)
        end_minutes = total_minutes + 30
        end_hours = 9 + end_minutes // 60
        end_minutes = end_minutes % 60
        end_time = f"{end_hours:02d}:{end_minutes:02d}"
        
        # Output the solution
        print("SOLUTION:")
        print(f"Day: {day_name}")
        print(f"Start Time: {start_time}")
        print(f"End Time: {end_time}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()