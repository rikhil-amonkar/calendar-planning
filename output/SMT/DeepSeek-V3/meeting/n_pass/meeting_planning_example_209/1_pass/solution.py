from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Solver()
    
    # Convert all times to minutes since 9:00 AM (540 minutes since midnight)
    # 9:00 AM is 540 minutes (9 * 60)
    # Define variables for start and end times of each meeting and travels
    
    # Meeting Melissa in North Beach
    melissa_start = Int('melissa_start')
    melissa_end = Int('melissa_end')
    melissa_min_duration = 105
    
    # Meeting Anthony in Chinatown
    anthony_start = Int('anthony_start')
    anthony_end = Int('anthony_end')
    anthony_min_duration = 60
    
    # Meeting Rebecca in Russian Hill
    rebecca_start = Int('rebecca_start')
    rebecca_end = Int('rebecca_end')
    rebecca_min_duration = 105
    
    # Time bounds for each friend's availability
    # Melissa: 8:15 AM (495) to 1:30 PM (810)
    melissa_available_start = 495
    melissa_available_end = 810
    
    # Anthony: 1:15 PM (795) to 2:30 PM (870)
    anthony_available_start = 795
    anthony_available_end = 870
    
    # Rebecca: 7:30 PM (1170) to 9:15 PM (1275)
    rebecca_available_start = 1170
    rebecca_available_end = 1275
    
    # Start at Sunset District at 9:00 AM (540)
    current_time = 540
    
    # Travel times (in minutes)
    # From Sunset to North Beach: 29
    sunset_to_north_beach = 29
    
    # From North Beach to Chinatown: 6
    north_beach_to_chinatown = 6
    
    # From Chinatown to Russian Hill: 7
    chinatown_to_russian_hill = 7
    
    # Constraints for Melissa
    s.add(melissa_start >= melissa_available_start)
    s.add(melissa_end <= melissa_available_end)
    s.add(melissa_end - melissa_start >= melissa_min_duration)
    
    # The trip to meet Melissa starts at current_time (540) and takes 29 minutes
    s.add(melissa_start >= current_time + sunset_to_north_beach)
    
    # Constraints for Anthony
    s.add(anthony_start >= anthony_available_start)
    s.add(anthony_end <= anthony_available_end)
    s.add(anthony_end - anthony_start >= anthony_min_duration)
    
    # Travel from North Beach to Chinatown after meeting Melissa
    s.add(anthony_start >= melissa_end + north_beach_to_chinatown)
    
    # Constraints for Rebecca
    s.add(rebecca_start >= rebecca_available_start)
    s.add(rebecca_end <= rebecca_available_end)
    s.add(rebecca_end - rebecca_start >= rebecca_min_duration)
    
    # Travel from Chinatown to Russian Hill after meeting Anthony
    s.add(rebecca_start >= anthony_end + chinatown_to_russian_hill)
    
    # Check if the constraints are satisfiable
    if s.check() == sat:
        m = s.model()
        # Extract the values
        melissa_s = m.eval(melissa_start).as_long()
        melissa_e = m.eval(melissa_end).as_long()
        anthony_s = m.eval(anthony_start).as_long()
        anthony_e = m.eval(anthony_end).as_long()
        rebecca_s = m.eval(rebecca_start).as_long()
        rebecca_e = m.eval(rebecca_end).as_long()
        
        # Convert minutes back to time strings
        def minutes_to_time(minutes):
            hours = minutes // 60
            mins = minutes % 60
            ampm = "AM" if hours < 12 else "PM"
            if hours > 12:
                hours -= 12
            return f"{hours}:{mins:02d} {ampm}"
        
        print("SOLUTION:")
        print(f"Meet Melissa in North Beach from {minutes_to_time(melissa_s)} to {minutes_to_time(melissa_e)}")
        print(f"Meet Anthony in Chinatown from {minutes_to_time(anthony_s)} to {minutes_to_time(anthony_e)}")
        print(f"Meet Rebecca in Russian Hill from {minutes_to_time(rebecca_s)} to {minutes_to_time(rebecca_e)}")
    else:
        print("No feasible schedule found.")

solve_scheduling()