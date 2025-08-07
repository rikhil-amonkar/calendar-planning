from z3 import *
import json

def main():
    # Initialize the optimizer
    opt = Optimize()
    
    # Define variables in minutes (from midnight)
    leave_time = Int('leave_time')  # When we leave Golden Gate Park
    S = Int('S')                   # Meeting start time
    
    # Constraints
    opt.add(leave_time >= 540)       # Must leave after 9:00 AM
    opt.add(S >= leave_time + 23)    # Travel time to Chinatown
    opt.add(S >= 960)                # Meeting must start at or after 4:00 PM
    opt.add(S <= 1200)               # Meeting must start by 8:00 PM to end by 9:45 PM (1200 + 105 = 1305 minutes)
    
    # Objective: minimize the meeting start time
    opt.minimize(S)
    
    # Check for a solution
    if opt.check() == sat:
        m = opt.model()
        start_minutes = m[S].as_long()
        # Convert start time to HH:MM format
        start_hours = start_minutes // 60
        start_mins = start_minutes % 60
        start_time = f"{start_hours:02d}:{start_mins:02d}"
        
        # Calculate end time (start + 105 minutes)
        end_minutes = start_minutes + 105
        end_hours = end_minutes // 60
        end_mins = end_minutes % 60
        end_time = f"{end_hours:02d}:{end_mins:02d}"
        
        # Create the itinerary
        itinerary = [
            {"action": "meet", "person": "David", "start_time": start_time, "end_time": end_time}
        ]
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        # Fallback if no solution is found (though the problem should be solvable)
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()