from z3 import *

def main():
    # Initialize solver
    s = Solver()
    
    # Define variables for meeting start and end times (in minutes from 9:00)
    k_start = Int('k_start')
    k_end = Int('k_end')
    t_start = Int('t_start')
    t_end = Int('t_end')
    
    # Convert time windows to minutes from 9:00
    k_available_start = 180  # 12:00
    k_available_end = 405    # 15:45
    t_available_start = 390  # 15:30
    t_available_end = 615    # 19:15
    
    # Travel times (minutes)
    travel_nob_to_mission = 13
    travel_mission_to_pacific = 16
    travel_nob_to_pacific = 8
    travel_pacific_to_mission = 15
    
    # Meeting duration constraints
    k_duration = 45
    t_duration = 75
    
    # Define constraints for both possible meeting orders
    order1 = And(
        # Kenneth meeting constraints
        k_start >= travel_nob_to_mission,
        k_start >= k_available_start,
        k_end == k_start + k_duration,
        k_end <= k_available_end,
        
        # Thomas meeting constraints
        t_start >= k_end + travel_mission_to_pacific,
        t_start >= t_available_start,
        t_end == t_start + t_duration,
        t_end <= t_available_end
    )
    
    order2 = And(
        # Thomas meeting constraints
        t_start >= travel_nob_to_pacific,
        t_start >= t_available_start,
        t_end == t_start + t_duration,
        t_end <= t_available_end,
        
        # Kenneth meeting constraints
        k_start >= t_end + travel_pacific_to_mission,
        k_start >= k_available_start,
        k_end == k_start + k_duration,
        k_end <= k_available_end
    )
    
    # Try both orders
    if s.check(order1) == sat:
        m = s.model()
    elif s.check(order2) == sat:
        m = s.model()
    else:
        # If no schedule found, return empty itinerary
        print('{"itinerary": []}')
        return
    
    # Extract values from model
    k_start_val = m.evaluate(k_start).as_long()
    k_end_val = m.evaluate(k_end).as_long()
    t_start_val = m.evaluate(t_start).as_long()
    t_end_val = m.evaluate(t_end).as_long()
    
    # Convert minutes to time strings
    def format_time(minutes):
        total_minutes = minutes
        hours = total_minutes // 60
        mins = total_minutes % 60
        return f"{9 + hours}:{mins:02d}"
    
    # Create itinerary
    itinerary = [
        {
            "action": "meet",
            "location": "Mission District",
            "person": "Kenneth",
            "start_time": format_time(k_start_val),
            "end_time": format_time(k_end_val)
        },
        {
            "action": "meet",
            "location": "Pacific Heights",
            "person": "Thomas",
            "start_time": format_time(t_start_val),
            "end_time": format_time(t_end_val)
        }
    ]
    
    # Output as JSON
    import json
    print(json.dumps({"itinerary": itinerary}, indent=2))

if __name__ == "__main__":
    main()