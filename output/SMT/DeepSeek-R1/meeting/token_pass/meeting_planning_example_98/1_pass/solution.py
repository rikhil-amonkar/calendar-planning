from z3 import *
import json

def main():
    # Convert all times to minutes since midnight
    start_time_min = 9 * 60  # 9:00 AM
    timothy_available_start = 20 * 60 + 45  # 20:45
    timothy_available_end = 21 * 60 + 30  # 21:30
    travel_to_richmond = 12
    travel_from_richmond = 13  # Not used in this scenario
    
    # Create Z3 variables
    leave_alamo = Int('leave_alamo')
    arrive_richmond = Int('arrive_richmond')
    meeting_start = Int('meeting_start')
    meeting_end = Int('meeting_end')
    
    # Initialize solver with optimization
    opt = Optimize()
    
    # Add constraints
    opt.add(leave_alamo >= start_time_min)
    opt.add(arrive_richmond == leave_alamo + travel_to_richmond)
    opt.add(meeting_start >= arrive_richmond)
    opt.add(meeting_start >= timothy_available_start)
    opt.add(meeting_end == meeting_start + 45)
    opt.add(meeting_end <= timothy_available_end)
    
    # Maximize meeting duration (though fixed at 45) and minimize waiting time
    opt.maximize(meeting_start)  # Start as early as possible within constraints
    
    # Check feasibility
    if opt.check() == sat:
        m = opt.model()
        meet_start_val = m[meeting_start].as_long()
        meet_end_val = meet_start_val + 45
        
        # Convert minutes back to time strings
        def format_time(minutes):
            hours = minutes // 60
            mins = minutes % 60
            return f"{hours}:{mins:02d}"
        
        itinerary = [{
            "action": "meet",
            "location": "Richmond District",
            "person": "Timothy",
            "start_time": format_time(meet_start_val),
            "end_time": format_time(meet_end_val)
        }]
        
        print(json.dumps({"itinerary": itinerary}))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()