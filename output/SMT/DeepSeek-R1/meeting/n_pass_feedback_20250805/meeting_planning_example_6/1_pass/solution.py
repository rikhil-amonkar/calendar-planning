from z3 import *
import json

def main():
    # Convert times to minutes from 9:00 AM
    kenneth_start_minutes = 5 * 60 + 15   # 14:15 (2:15 PM) -> 315 minutes
    kenneth_end_minutes = 10 * 60 + 45    # 19:45 (7:45 PM) -> 645 minutes
    meeting_duration = 90

    # Initialize solver
    s = Solver()
    meeting_start = Int('meeting_start')
    
    # Constraints
    s.add(meeting_start >= kenneth_start_minutes)
    s.add(meeting_start + meeting_duration <= kenneth_end_minutes)
    
    # Check for a solution
    if s.check() == sat:
        m = s.model()
        start_val = m[meeting_start].as_long()
        
        # Calculate end time in minutes
        end_val = start_val + meeting_duration
        
        # Convert start time to HH:MM format
        total_minutes_start = start_val
        hours_start = total_minutes_start // 60
        minutes_start = total_minutes_start % 60
        start_hour = 9 + hours_start
        start_time_str = f"{start_hour:02d}:{minutes_start:02d}"
        
        # Convert end time to HH:MM format
        total_minutes_end = end_val
        hours_end = total_minutes_end // 60
        minutes_end = total_minutes_end % 60
        end_hour = 9 + hours_end
        end_time_str = f"{end_hour:02d}:{minutes_end:02d}"
        
        # Create itinerary
        itinerary = [
            {
                "action": "meet",
                "person": "Kenneth",
                "start_time": start_time_str,
                "end_time": end_time_str
            }
        ]
        
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()