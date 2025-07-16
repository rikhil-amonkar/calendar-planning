from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Solver()
    
    # Define variables (all times in minutes since midnight)
    # We start at Alamo Square at 9:00 AM (540 minutes since midnight)
    start_time = 540
    
    # Convert all times to minutes since midnight for consistency
    # Timothy's availability: 8:45 PM (1260) to 9:30 PM (1290)
    timothy_start = 1260
    timothy_end = 1290
    
    # Decision variables
    leave_alamo = Int('leave_alamo')          # When we leave Alamo Square
    arrive_richmond = Int('arrive_richmond')  # When we arrive at Richmond
    leave_richmond = Int('leave_richmond')    # When we leave Richmond
    
    # Add constraints
    # 1. We can't leave Alamo Square before 9:00 AM
    s.add(leave_alamo >= start_time)
    
    # 2. Travel time to Richmond is 12 minutes
    s.add(arrive_richmond == leave_alamo + 12)
    
    # 3. Must meet Timothy for at least 45 minutes
    s.add(leave_richmond >= arrive_richmond + 45)
    
    # 4. Must arrive during Timothy's availability window
    s.add(arrive_richmond >= timothy_start)
    s.add(arrive_richmond <= timothy_end - 45)  # Ensure we can stay 45 mins
    
    # 5. Must leave during Timothy's availability window
    s.add(leave_richmond >= timothy_start + 45)
    s.add(leave_richmond <= timothy_end)
    
    # Find any valid solution
    if s.check() == sat:
        m = s.model()
        
        # Convert minutes to readable time
        def min_to_time(minutes):
            hours = minutes // 60
            mins = minutes % 60
            period = "AM" if hours < 12 else "PM"
            if hours > 12:
                hours -= 12
            return f"{hours}:{mins:02d} {period}"
        
        # Print results
        print("Valid schedule found:")
        print(f"Leave Alamo Square at: {min_to_time(m[leave_alamo].as_long())}")
        print(f"Arrive Richmond District at: {min_to_time(m[arrive_richmond].as_long())}")
        print(f"Leave Richmond District at: {min_to_time(m[leave_richmond].as_long())}")
        print(f"Meeting duration: {m[leave_richmond].as_long() - m[arrive_richmond].as_long()} minutes")
    else:
        print("No valid schedule found that meets all constraints")

solve_scheduling()