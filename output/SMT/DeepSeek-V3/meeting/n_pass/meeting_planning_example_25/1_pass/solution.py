from z3 import *
import json

def solve_scheduling():
    # Initialize Z3 solver
    s = Solver()
    
    # Variables for meeting start and end times in minutes since 9:00 AM
    meet_start = Int('meet_start')
    meet_end = Int('meet_end')
    
    # Convert all times to minutes since 9:00 AM (540 minutes since midnight)
    # David's availability: 4:00 PM to 9:45 PM is 16:00 to 21:45 in 24-hour format
    david_start = (16 * 60) - (9 * 60)  # 16:00 is 7 hours after 9:00, 420 minutes
    david_end = (21 * 60 + 45) - (9 * 60)  # 21:45 is 12 hours and 45 minutes after 9:00, 765 minutes
    
    travel_time = 23  # minutes to Chinatown
    
    # Constraints
    # 1. You can leave Golden Gate Park after 9:00 AM (time >= 0)
    leave_time = meet_start - travel_time  # you leave Golden Gate Park at meet_start - travel_time
    s.add(leave_time >= 0)
    
    # 2. Meeting must be within David's availability
    s.add(meet_start >= david_start)
    s.add(meet_end <= david_end)
    
    # 3. Meeting duration is at least 105 minutes
    s.add(meet_end - meet_start >= 105)
    
    # 4. meet_end is meet_start + duration (implied by meet_end - meet_start >= 105)
    
    # Optimize for the earliest possible meeting to free up the rest of the day
    s.push()
    s.add(meet_start == david_start)  # earliest possible meeting start
    if s.check() == sat:
        m = s.model()
        start = m[meet_start].as_long()
        end = m[meet_end].as_long()
        
        # Convert back to HH:MM format
        def to_time_str(minutes_since_9am):
            total_minutes = 9 * 60 + minutes_since_9am
            hours = total_minutes // 60
            minutes = total_minutes % 60
            return f"{hours:02d}:{minutes:02d}"
        
        start_time = to_time_str(start)
        end_time = to_time_str(end)
        
        itinerary = [{
            "action": "meet",
            "person": "David",
            "start_time": start_time,
            "end_time": end_time
        }]
        
        print(json.dumps({"itinerary": itinerary}, indent=2))
    else:
        print("No valid schedule found.")

solve_scheduling()