from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Solver()
    
    # Convert all times to minutes since midnight for consistency
    start_time = 9 * 60  # 9:00 AM (540 minutes)
    timothy_start = 20 * 60 + 45  # 8:45 PM (1260 minutes)
    timothy_end = 21 * 60 + 30  # 9:30 PM (1290 minutes)
    travel_to = 12  # Minutes to Richmond
    travel_back = 13  # Minutes back to Alamo
    
    # Decision variables (in minutes since midnight)
    leave_alamo = Int('leave_alamo')
    arrive_richmond = Int('arrive_richmond')
    leave_richmond = Int('leave_richmond')
    arrive_back = Int('arrive_back')
    
    # Add constraints
    # 1. Must leave Alamo Square no earlier than 9:00 AM
    s.add(leave_alamo >= start_time)
    
    # 2. Travel time to Richmond is 12 minutes
    s.add(arrive_richmond == leave_alamo + travel_to)
    
    # 3. Must meet Timothy for exactly 45 minutes
    s.add(leave_richmond == arrive_richmond + 45)
    
    # 4. Must arrive during Timothy's availability window
    s.add(arrive_richmond >= timothy_start)
    s.add(leave_richmond <= timothy_end)
    
    # 5. Travel time back to Alamo is 13 minutes
    s.add(arrive_back == leave_richmond + travel_back)
    
    # Find any valid solution
    if s.check() == sat:
        m = s.model()
        
        def format_time(minutes):
            h = minutes // 60
            m = minutes % 60
            period = "AM" if h < 12 else "PM"
            h = h % 12
            h = 12 if h == 0 else h
            return f"{h}:{m:02d} {period}"
        
        print("\nOptimal Schedule:")
        print(f"1. Leave Alamo Square at: {format_time(m[leave_alamo].as_long())}")
        print(f"2. Arrive Richmond District at: {format_time(m[arrive_richmond].as_long())}")
        print(f"3. Meet Timothy from: {format_time(m[arrive_richmond].as_long())} to {format_time(m[leave_richmond].as_long())}")
        print(f"4. Return to Alamo Square at: {format_time(m[arrive_back].as_long())}")
        print(f"\nTotal meeting time: 45 minutes (as required)")
    else:
        print("No valid schedule found that meets all constraints")

solve_scheduling()