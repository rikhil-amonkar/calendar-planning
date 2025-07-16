from z3 import *

def solve_scheduling():
    # Create a solver instance
    s = Solver()
    
    # Define variables
    # Time to leave Alamo Square to go to Richmond District (in minutes since 9:00 AM)
    leave_alamo = Int('leave_alamo')
    
    # Time to arrive at Richmond District (in minutes since 9:00 AM)
    arrive_richmond = Int('arrive_richmond')
    
    # Time to leave Richmond District (in minutes since 9:00 AM)
    leave_richmond = Int('leave_richmond')
    
    # Time to arrive back at Alamo Square (in minutes since 9:00 AM)
    arrive_back_alamo = Int('arrive_back_alamo')
    
    # Constraints
    
    # Travel time from Alamo Square to Richmond District is 12 minutes
    s.add(arrive_richmond == leave_alamo + 12)
    
    # Meeting duration is at least 45 minutes
    s.add(leave_richmond >= arrive_richmond + 45)
    
    # Timothy is available from 8:45 PM to 9:30 PM (convert to minutes since 9:00 AM)
    # 9:00 AM to 8:45 PM is 11 hours and 45 minutes = 705 minutes
    # 9:00 AM to 9:30 PM is 12 hours and 30 minutes = 750 minutes
    s.add(arrive_richmond >= 705)  # Arrive by 8:45 PM
    s.add(leave_richmond <= 750)   # Leave by 9:30 PM
    
    # Travel time back to Alamo Square is 13 minutes
    s.add(arrive_back_alamo == leave_richmond + 13)
    
    # We start at Alamo Square at 9:00 AM (time 0)
    s.add(leave_alamo >= 0)
    
    # The goal is to maximize the time spent with Timothy, which is at least 45 minutes
    # Since the constraints already enforce at least 45 minutes, we can just check satisfiability
    
    # Check if the constraints are satisfiable
    if s.check() == sat:
        m = s.model()
        print("Solution found:")
        print(f"Leave Alamo Square at: {m[leave_alamo].as_long()} minutes after 9:00 AM")
        print(f"Arrive at Richmond District at: {m[arrive_richmond].as_long()} minutes after 9:00 AM")
        print(f"Leave Richmond District at: {m[leave_richmond].as_long()} minutes after 9:00 AM")
        print(f"Arrive back at Alamo Square at: {m[arrive_back_alamo].as_long()} minutes after 9:00 AM")
        
        # Convert minutes to human-readable time
        def minutes_to_time(minutes):
            hours = 9 + minutes // 60
            mins = minutes % 60
            ampm = "AM" if hours < 12 else "PM"
            if hours > 12:
                hours -= 12
            return f"{hours}:{mins:02d} {ampm}"
        
        print("\nHuman-readable times:")
        print(f"Leave Alamo Square at: {minutes_to_time(m[leave_alamo].as_long())}")
        print(f"Arrive at Richmond District at: {minutes_to_time(m[arrive_richmond].as_long())}")
        print(f"Leave Richmond District at: {minutes_to_time(m[leave_richmond].as_long())}")
        print(f"Arrive back at Alamo Square at: {minutes_to_time(m[arrive_back_alamo].as_long())}")
    else:
        print("No solution found")

solve_scheduling()