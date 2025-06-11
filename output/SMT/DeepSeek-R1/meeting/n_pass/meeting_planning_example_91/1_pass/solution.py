from z3 import *

def main():
    # Initialize solver
    s = Solver()
    
    # Departure time from Russian Hill (minutes after 9:00 AM)
    depart_RH = Int('depart_RH')
    
    # Constraints
    s.add(depart_RH >= 0)  # Departure time cannot be negative
    s.add(depart_RH + 14 <= 600)  # Must arrive by 7:00 PM (600 minutes after 9:00 AM)
    
    # Check for a solution
    if s.check() == sat:
        m = s.model()
        depart_val = m[depart_RH].as_long()
        
        # Convert minutes to time format
        total_minutes = depart_val
        hours = total_minutes // 60
        minutes = total_minutes % 60
        total_hours = 9 + hours  # Starting from 9:00 AM
        
        # Convert to 12-hour format with AM/PM
        if total_hours >= 12:
            suffix = "PM"
            if total_hours > 12:
                total_hours -= 12
        else:
            suffix = "AM"
        
        print(f"Depart Russian Hill at {total_hours}:{minutes:02d} {suffix}.")
    else:
        print("No valid schedule found.")

if __name__ == "__main__":
    main()