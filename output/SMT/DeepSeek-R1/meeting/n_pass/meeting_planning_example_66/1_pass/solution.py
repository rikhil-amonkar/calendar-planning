from z3 import *
import json

def main():
    # Convert times to minutes from midnight
    start_nob_hill = 9 * 60  # 9:00 AM (540 minutes)
    robert_start = 11 * 60 + 15  # 11:15 AM (675 minutes)
    robert_end = 17 * 60 + 45    # 5:45 PM (1065 minutes)
    travel_to_presidio = 17       # Travel time in minutes

    # Define meeting start (S) and end (E) times
    S = Int('S')
    E = Int('E')
    
    s = Solver()
    # Meeting must occur during Robert's availability
    s.add(S >= robert_start)
    s.add(E <= robert_end)
    # Meeting duration must be at least 120 minutes
    s.add(E - S >= 120)
    # Account for travel time: meeting start must be after arrival at Presidio
    s.add(S >= start_nob_hill + travel_to_presidio)
    
    # Optimize to find earliest possible meeting
    opt = Optimize()
    opt.add(s.assertions())
    opt.minimize(S)  # Prefer earlier start times
    
    if opt.check() == sat:
        m = opt.model()
        start_minutes = m[S].as_long()
        end_minutes = m[E].as_long()
        
        # Convert minutes back to HH:MM format
        def format_time(minutes):
            hours = minutes // 60
            mins = minutes % 60
            return f"{hours:02d}:{mins:02d}"
        
        start_str = format_time(start_minutes)
        end_str = format_time(end_minutes)
        
        # Create itinerary
        itinerary = [{
            "action": "meet",
            "person": "Robert",
            "start_time": start_str,
            "end_time": end_str
        }]
        
        # Output as JSON
        print(json.dumps({"itinerary": itinerary}))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()