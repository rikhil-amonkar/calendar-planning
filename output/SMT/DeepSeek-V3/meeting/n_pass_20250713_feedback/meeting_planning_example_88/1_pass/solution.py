from z3 import *

def solve_scheduling():
    # Create a solver instance
    s = Solver()
    
    # Define variables
    # Time you leave Sunset District to go to Golden Gate Park (in minutes since 9:00 AM)
    leave_sunset = Int('leave_sunset')
    
    # Time you arrive at Golden Gate Park
    arrive_golden_gate = Int('arrive_golden_gate')
    
    # Time you leave Golden Gate Park to return to Sunset District
    leave_golden_gate = Int('leave_golden_gate')
    
    # Time you arrive back at Sunset District
    arrive_sunset = Int('arrive_sunset')
    
    # Time spent with Joshua (in minutes)
    meet_time = 15
    
    # Travel times (in minutes)
    sunset_to_golden_gate = 11
    golden_gate_to_sunset = 10
    
    # Joshua's availability window (in minutes since 9:00 AM)
    joshua_start = (12 * 60) + 45 - (9 * 60)  # 8:45 PM is 11 hours and 45 minutes after 9:00 AM
    joshua_end = (12 * 60) + 45 - (9 * 60) + 60  # 9:45 PM is 1 hour after 8:45 PM
    
    # Constraints
    # You can leave Sunset District any time after arriving (9:00 AM, i.e., 0 minutes)
    s.add(leave_sunset >= 0)
    
    # Arrival at Golden Gate Park is leave_sunset + travel time
    s.add(arrive_golden_gate == leave_sunset + sunset_to_golden_gate)
    
    # You must arrive at Golden Gate Park before Joshua leaves (9:45 PM)
    s.add(arrive_golden_gate <= joshua_end)
    
    # You must leave Golden Gate Park after arriving
    s.add(leave_golden_gate >= arrive_golden_gate)
    
    # You must meet Joshua for at least 15 minutes
    s.add(leave_golden_gate >= arrive_golden_gate + meet_time)
    
    # You must leave Golden Gate Park before Joshua's window ends (9:45 PM)
    s.add(leave_golden_gate <= joshua_end)
    
    # Arrival back at Sunset District is leave_golden_gate + return travel time
    s.add(arrive_sunset == leave_golden_gate + golden_gate_to_sunset)
    
    # Check if there's a solution
    if s.check() == sat:
        m = s.model()
        print("Solution found:")
        print(f"Leave Sunset District at: {m[leave_sunset].as_long()} minutes after 9:00 AM")
        print(f"Arrive at Golden Gate Park at: {m[arrive_golden_gate].as_long()} minutes after 9:00 AM")
        print(f"Leave Golden Gate Park at: {m[leave_golden_gate].as_long()} minutes after 9:00 AM")
        print(f"Arrive back at Sunset District at: {m[arrive_sunset].as_long()} minutes after 9:00 AM")
    else:
        print("No solution exists.")

solve_scheduling()