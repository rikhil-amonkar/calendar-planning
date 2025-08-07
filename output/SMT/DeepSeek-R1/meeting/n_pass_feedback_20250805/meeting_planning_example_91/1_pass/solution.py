from z3 import *
import json

def main():
    # Convert times to minutes from midnight
    start_of_day = 9 * 60  # 9:00 AM = 540 minutes
    daniel_available_start = 19 * 60  # 19:00 = 1140 minutes
    daniel_available_end = 20 * 60 + 15  # 20:15 = 1215 minutes
    travel_to_daniel = 14  # Travel time in minutes

    # Initialize solver
    s = Solver()
    
    # Define meeting start and end times
    d_start = Int('d_start')
    d_end = Int('d_end')
    
    # Constraints
    s.add(d_start >= daniel_available_start)  # Meeting must start when Daniel is available
    s.add(d_end <= daniel_available_end)      # Meeting must end when Daniel is available
    s.add(d_end - d_start >= 75)              # Meeting duration at least 75 minutes
    s.add(d_start - travel_to_daniel >= start_of_day)  # Travel must start after 9:00 AM

    # Check for a solution
    if s.check() == sat:
        m = s.model()
        start_min = m[d_start].as_long()
        end_min = m[d_end].as_long()
        
        # Convert to HH:MM format
        start_hour = start_min // 60
        start_minute = start_min % 60
        end_hour = end_min // 60
        end_minute = end_min % 60
        
        start_time = f"{start_hour:02d}:{start_minute:02d}"
        end_time = f"{end_hour:02d}:{end_minute:02d}"
        
        itinerary = [
            {"action": "meet", "person": "Daniel", "start_time": start_time, "end_time": end_time}
        ]
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()