from z3 import *
import json

def main():
    # Create the variables
    carol_start = Int('carol_start')
    jessica_start = Int('jessica_start')
    jessica_duration = Int('jessica_duration')
    
    opt = Optimize()
    
    # Carol must start between 11:30 AM (150 minutes from 9:00 AM) and 2:00 PM (300 minutes from 9:00 AM)
    opt.add(carol_start >= 150)
    opt.add(carol_start <= 300)
    
    # Jessica must start at or after 3:30 PM (390 minutes from 9:00 AM)
    opt.add(jessica_start >= 390)
    # Jessica's meeting must last at least 45 minutes and end by 4:45 PM (465 minutes from 9:00 AM)
    opt.add(jessica_duration >= 45)
    opt.add(jessica_start + jessica_duration <= 465)
    
    # Travel constraint: after meeting Carol (ends at carol_start + 60), travel to Pacific Heights takes 7 minutes
    opt.add(carol_start + 60 + 7 <= jessica_start)
    
    # Objectives: first maximize Jessica's meeting duration, then maximize Carol's start time (to minimize waiting)
    opt.maximize(jessica_duration)
    opt.maximize(carol_start)
    
    result = {"itinerary": []}
    if opt.check() == sat:
        m = opt.model()
        carol_start_val = m[carol_start].as_long()
        jessica_start_val = m[jessica_start].as_long()
        jessica_duration_val = m[jessica_duration].as_long()
        
        # Compute Carol's meeting times
        carol_start_minutes = carol_start_val
        carol_start_hour = 9 + carol_start_minutes // 60
        carol_start_minute = carol_start_minutes % 60
        carol_end_minutes = carol_start_minutes + 60
        carol_end_hour = 9 + carol_end_minutes // 60
        carol_end_minute = carol_end_minutes % 60
        
        # Compute Jessica's meeting times
        jessica_start_minutes = jessica_start_val
        jessica_start_hour = 9 + jessica_start_minutes // 60
        jessica_start_minute = jessica_start_minutes % 60
        jessica_end_minutes = jessica_start_minutes + jessica_duration_val
        jessica_end_hour = 9 + jessica_end_minutes // 60
        jessica_end_minute = jessica_end_minutes % 60
        
        # Format as HH:MM strings
        carol_start_str = f"{carol_start_hour:02d}:{carol_start_minute:02d}"
        carol_end_str = f"{carol_end_hour:02d}:{carol_end_minute:02d}"
        jessica_start_str = f"{jessica_start_hour:02d}:{jessica_start_minute:02d}"
        jessica_end_str = f"{jessica_end_hour:02d}:{jessica_end_minute:02d}"
        
        itinerary = [
            {"action": "meet", "person": "Carol", "start_time": carol_start_str, "end_time": carol_end_str},
            {"action": "meet", "person": "Jessica", "start_time": jessica_start_str, "end_time": jessica_end_str}
        ]
        result = {"itinerary": itinerary}
    
    print("SOLUTION:")
    print(json.dumps(result))

if __name__ == "__main__":
    main()