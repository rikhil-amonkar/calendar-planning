from z3 import *
import json

def main():
    s = Solver()
    
    # Define the start time for Emily's meeting in minutes from 9:00 AM
    emily_start = Int('emily_start')
    emily_duration = 45
    margaret_start = 600  # 19:00 (7:00 PM) in minutes from 9:00 AM
    margaret_end = 720    # 21:00 (9:00 PM)
    
    # Emily must meet between 16:00 (420 minutes) and 17:15 (495 minutes)
    s.add(emily_start >= 420)
    s.add(emily_start + emily_duration <= 495)
    
    # Travel constraints
    # Start at NB at 0 minutes (9:00 AM), travel to US for Emily: 7 minutes
    s.add(emily_start - 7 >= 0)
    # After Emily, travel from US to RH: 13 minutes, must arrive by 19:00 (600 minutes)
    s.add(emily_start + emily_duration + 13 <= margaret_start)
    
    if s.check() == sat:
        m = s.model()
        emily_s = m[emily_start].as_long()
        
        # Convert Emily's meeting times to HH:MM format
        emily_start_hour = 9 + emily_s // 60
        emily_start_minute = emily_s % 60
        emily_end_s = emily_s + emily_duration
        emily_end_hour = 9 + emily_end_s // 60
        emily_end_minute = emily_end_s % 60
        
        emily_start_time = f"{emily_start_hour:02d}:{emily_start_minute:02d}"
        emily_end_time = f"{emily_end_hour:02d}:{emily_end_minute:02d}"
        
        # Margaret's meeting times are fixed
        margaret_start_time = "19:00"
        margaret_end_time = "21:00"
        
        # Construct itinerary
        itinerary = [
            {"action": "meet", "person": "Emily", "start_time": emily_start_time, "end_time": emily_end_time},
            {"action": "meet", "person": "Margaret", "start_time": margaret_start_time, "end_time": margaret_end_time}
        ]
        
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()