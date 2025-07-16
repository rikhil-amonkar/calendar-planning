from z3 import *

def solve_scheduling():
    # Create solver instance
    s = Solver()
    
    # Define variables (all times in minutes since 9:00 AM)
    leave_alamo = Int('leave_alamo')          # When we leave Alamo Square
    arrive_richmond = Int('arrive_richmond')  # When we arrive at Richmond District
    leave_richmond = Int('leave_richmond')    # When we leave Richmond District
    
    # Add constraints
    
    # 1. Travel time to Richmond is 12 minutes
    s.add(arrive_richmond == leave_alamo + 12)
    
    # 2. Must meet Timothy for at least 45 minutes
    s.add(leave_richmond >= arrive_richmond + 45)
    
    # 3. Timothy's availability window (8:45 PM to 9:30 PM)
    # Convert to minutes since 9:00 AM:
    # 8:45 PM is 11 hours 45 minutes = 705 minutes
    # 9:30 PM is 12 hours 30 minutes = 750 minutes
    s.add(arrive_richmond >= 705)   # Must arrive by 8:45 PM
    s.add(leave_richmond <= 750)    # Must leave by 9:30 PM
    
    # 4. Can't leave Alamo Square before 9:00 AM (time 0)
    s.add(leave_alamo >= 0)
    
    # 5. Additional constraint: leave Richmond after arriving
    s.add(leave_richmond > arrive_richmond)
    
    # Find earliest possible departure from Alamo Square
    # We want to minimize leave_alamo to maximize time in Alamo Square
    s.push()
    s.minimize(leave_alamo)
    
    if s.check() == sat:
        m = s.model()
        print("Optimal schedule found:")
        
        # Convert minutes to readable time format
        def format_time(minutes):
            total_hours = 9 + minutes // 60
            hour = total_hours % 12
            if hour == 0:
                hour = 12
            minute = minutes % 60
            period = "AM" if total_hours < 12 else "PM"
            return f"{hour}:{minute:02d} {period}"
        
        # Print results
        print(f"Leave Alamo Square at: {format_time(m[leave_alamo].as_long())}")
        print(f"Arrive Richmond District at: {format_time(m[arrive_richmond].as_long())}")
        print(f"Leave Richmond District at: {format_time(m[leave_richmond].as_long())}")
        print(f"Meeting duration: {m[leave_richmond].as_long() - m[arrive_richmond].as_long()} minutes")
    else:
        print("No valid schedule found")
    
    s.pop()

solve_scheduling()