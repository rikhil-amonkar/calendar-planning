from z3 import *

def main():
    # Create solver
    s = Solver()
    
    # Define variables for meeting start times (in minutes from 9:00 AM)
    T_start = Int('T_start')  # Timothy start time
    J_start = Int('J_start')  # Joseph start time
    M_start = Int('M_start')  # Mark start time
    
    # Fixed meeting durations (minimum required)
    T_dur = 105  # Timothy
    J_dur = 60   # Joseph
    M_dur = 60   # Mark
    
    # Constraints for Timothy (Alamo Square: 12:00 to 16:15)
    s.add(T_start >= 180)        # 12:00 PM is 180 minutes from 9:00 AM
    s.add(T_start + T_dur <= 435)  # 16:15 is 435 minutes from 9:00 AM
    
    # Constraints for Joseph (Russian Hill: 16:45 to 21:30)
    s.add(J_start >= 465)        # 16:45 is 465 minutes from 9:00 AM
    s.add(J_start + J_dur <= 750)  # 21:30 is 750 minutes from 9:00 AM
    
    # Constraints for Mark (Presidio: 18:45 to 21:00)
    s.add(M_start >= 585)        # 18:45 is 585 minutes from 9:00 AM
    s.add(M_start + M_dur <= 720)  # 21:00 is 720 minutes from 9:00 AM
    
    # Travel constraints
    # Start at Golden Gate Park at 0 minutes (9:00 AM). Travel to Alamo Square takes 10 minutes.
    s.add(T_start - 10 >= 0)  # Departure time from Golden Gate Park must be non-negative
    
    # Travel from Alamo Square (after meeting Timothy) to Russian Hill takes 13 minutes
    s.add(J_start >= T_start + T_dur + 13)  # Arrival at Russian Hill must be after travel
    
    # Travel from Russian Hill (after meeting Joseph) to Presidio takes 14 minutes
    s.add(M_start >= J_start + J_dur + 14)  # Arrival at Presidio must be after travel
    
    # Check if the constraints are satisfiable
    if s.check() == sat:
        m = s.model()
        T_val = m.eval(T_start).as_long()
        J_val = m.eval(J_start).as_long()
        M_val = m.eval(M_start).as_long()
        
        # Calculate end times
        T_end = T_val + T_dur
        J_end = J_val + J_dur
        M_end = M_val + M_dur
        
        # Convert times to HH:MM format
        def to_time_str(minutes):
            total_minutes = minutes
            hours = total_minutes // 60
            mins = total_minutes % 60
            abs_hour = 9 + hours  # Since we start at 9:00 AM
            return f"{abs_hour:02d}:{mins:02d}"
        
        # Format meeting entries
        itinerary = [
            {"action": "meet", "person": "Timothy", "start_time": to_time_str(T_val), "end_time": to_time_str(T_end)},
            {"action": "meet", "person": "Joseph", "start_time": to_time_str(J_val), "end_time": to_time_str(J_end)},
            {"action": "meet", "person": "Mark", "start_time": to_time_str(M_val), "end_time": to_time_str(M_end)}
        ]
        
        # Output as JSON
        print({
            "itinerary": itinerary
        })
    else:
        print("No valid schedule found")

if __name__ == "__main__":
    main()