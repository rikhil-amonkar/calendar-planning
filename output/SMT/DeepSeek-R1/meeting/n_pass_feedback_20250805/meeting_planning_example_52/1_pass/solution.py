from z3 import *
import json

def main():
    # Convert times to minutes from midnight
    start_of_day = 9 * 60  # 9:00 AM = 540 minutes
    barbara_start_avail = 13 * 60 + 15  # 1:15 PM = 795 minutes
    barbara_end_avail = 18 * 60 + 15    # 6:15 PM = 1095 minutes
    travel_time_to_richmond = 14  # minutes

    # Create Z3 variables
    leave_rh = Int('leave_rh')  # Time leaving Russian Hill
    start_b = Int('start_b')    # Meeting start time with Barbara

    # Initialize solver with optimization
    s = Optimize()
    
    # Add constraints
    s.add(leave_rh >= start_of_day)
    s.add(start_b >= barbara_start_avail)
    s.add(start_b + 45 <= barbara_end_avail)  # Meeting duration is 45 minutes
    s.add(leave_rh + travel_time_to_richmond <= start_b)  # Travel constraint
    
    # Objective: minimize the meeting start time
    s.minimize(start_b)
    
    # Check for a solution
    if s.check() == sat:
        m = s.model()
        start_val = m[start_b].as_long()
        end_val = start_val + 45
        
        # Convert minutes back to HH:MM format
        def format_time(minutes):
            hours = minutes // 60
            mins = minutes % 60
            return f"{hours:02d}:{mins:02d}"
        
        start_time_str = format_time(start_val)
        end_time_str = format_time(end_val)
        
        # Create the itinerary
        itinerary = [
            {
                "action": "meet",
                "person": "Barbara",
                "start_time": start_time_str,
                "end_time": end_time_str
            }
        ]
        
        # Output as JSON-formatted dictionary
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()