from z3 import *
import json

def main():
    # Initialize the solver with optimization
    opt = Optimize()
    
    # Convert all times to minutes since midnight
    sunset_arrival = 9 * 60  # 9:00 AM
    joshua_start = 20 * 60 + 45  # 8:45 PM
    joshua_end = 21 * 60 + 45    # 9:45 PM
    
    # Travel times in minutes
    travel_to_park = 11
    travel_back = 10
    
    # Decision variables
    leave_sunset = Int('leave_sunset')
    arrive_park = Int('arrive_park')
    meet_start = Int('meet_start')
    meet_end = Int('meet_end')
    leave_park = Int('leave_park')
    
    # Constraints
    opt.add(leave_sunset >= sunset_arrival)  # Can't leave before arrival
    opt.add(arrive_park == leave_sunset + travel_to_park)
    opt.add(meet_start >= arrive_park)  # Can't meet before arriving
    opt.add(meet_start >= joshua_start)  # Joshua available from 8:45PM
    opt.add(meet_end <= joshua_end)      # Joshua available until 9:45PM
    opt.add(meet_end - meet_start >= 15) # Minimum 15 minute meeting
    
    # Maximize meeting duration
    meeting_duration = meet_end - meet_start
    opt.maximize(meeting_duration)
    
    # Check feasibility and get model
    if opt.check() == sat:
        m = opt.model()
        lv_sunset = m.evaluate(leave_sunset).as_long()
        m_start = m.evaluate(meet_start).as_long()
        m_end = m.evaluate(meet_end).as_long()
        
        # Convert times to formatted strings
        def format_time(minutes):
            hours = minutes // 60
            mins = minutes % 60
            return f"{hours}:{mins:02d}"
        
        itinerary = [{
            "action": "meet",
            "location": "Golden Gate Park",
            "person": "Joshua",
            "start_time": format_time(m_start),
            "end_time": format_time(m_end)
        }]
        
        print(json.dumps({"itinerary": itinerary}, indent=2))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()