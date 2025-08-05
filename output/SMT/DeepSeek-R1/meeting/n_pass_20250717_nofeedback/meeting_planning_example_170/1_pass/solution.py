from z3 import *
import json

def main():
    base_minutes = 9 * 60  # 9:00 AM in minutes from midnight
    s = Optimize()
    
    start_emily = Int('start_emily')
    start_margaret = 600  # 7:00 PM is 600 minutes from 9:00 AM
    
    s.add(start_emily >= 420)  # 4:00 PM
    s.add(start_emily <= 450)  # 4:30 PM
    s.add(0 + 7 <= start_emily)  # Travel from North Beach to Union Square (7 minutes)
    s.add(start_emily + 45 + 13 <= start_margaret)  # Meeting with Emily and travel to Russian Hill
    
    s.maximize(start_emily)  # Minimize waiting time at Russian Hill
    
    if s.check() == sat:
        m = s.model()
        emily_start_val = m[start_emily].as_long()
        
        # Convert Emily's meeting start and end times
        emily_start_abs = base_minutes + emily_start_val
        emily_start_hour = emily_start_abs // 60
        emily_start_minute = emily_start_abs % 60
        emily_start_str = f"{emily_start_hour:02d}:{emily_start_minute:02d}"
        
        emily_end_abs = emily_start_abs + 45
        emily_end_hour = emily_end_abs // 60
        emily_end_minute = emily_end_abs % 60
        emily_end_str = f"{emily_end_hour:02d}:{emily_end_minute:02d}"
        
        # Margaret's meeting is fixed
        margaret_start_abs = base_minutes + start_margaret
        margaret_end_abs = margaret_start_abs + 120
        
        margaret_start_hour = margaret_start_abs // 60
        margaret_start_minute = margaret_start_abs % 60
        margaret_start_str = f"{margaret_start_hour:02d}:{margaret_start_minute:02d}"
        
        margaret_end_hour = margaret_end_abs // 60
        margaret_end_minute = margaret_end_abs % 60
        margaret_end_str = f"{margaret_end_hour:02d}:{margaret_end_minute:02d}"
        
        itinerary = [
            {"action": "meet", "person": "Emily", "start_time": emily_start_str, "end_time": emily_end_str},
            {"action": "meet", "person": "Margaret", "start_time": margaret_start_str, "end_time": margaret_end_str}
        ]
        
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()