from z3 import *
import json

def main():
    # Create variables for departure time, meeting start, and meeting end (in minutes)
    leave_alamo = Int('leave_alamo')
    meet_start = Int('meet_start')
    meet_end = Int('meet_end')
    
    s = Solver()
    
    # Convert time constraints to minutes
    start_alamo = 9 * 60  # 9:00 AM
    timothy_start = 20 * 60 + 45  # 20:45
    timothy_end = 21 * 60 + 30   # 21:30
    min_meeting = 45  # minimum meeting duration in minutes
    
    # Constraints
    s.add(leave_alamo >= start_alamo)
    s.add(meet_start >= timothy_start)
    s.add(meet_end <= timothy_end)
    s.add(meet_end - meet_start >= min_meeting)
    s.add(leave_alamo + 12 <= meet_start)  # Travel time constraint
    
    if s.check() == sat:
        m = s.model()
        start_min = m[meet_start].as_long()
        end_min = m[meet_end].as_long()
        
        # Format to HH:MM
        start_hour = start_min // 60
        start_minute = start_min % 60
        end_hour = end_min // 60
        end_minute = end_min % 60
        
        start_str = f"{start_hour:02d}:{start_minute:02d}"
        end_str = f"{end_hour:02d}:{end_minute:02d}"
        
        itinerary = [{"action": "meet", "person": "Timothy", "start_time": start_str, "end_time": end_str}]
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()