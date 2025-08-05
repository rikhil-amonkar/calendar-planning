from z3 import *
import json

def main():
    # Convert times to minutes from midnight
    start_at_russian_hill = 9 * 60  # 9:00 AM
    travel_time = 7
    arrival_at_pacific_heights = start_at_russian_hill + travel_time  # 9:07 AM (547 minutes)
    barbara_available_start = 7 * 60 + 15  # 7:15 AM (435 minutes)
    barbara_available_end = 22 * 60  # 10:00 PM (1320 minutes)
    min_duration = 60  # 60 minutes

    # Initialize Z3 solver
    s = Optimize()
    start = Int('start')
    
    # Constraints
    s.add(start >= barbara_available_start)  # Cannot start before Barbara is available
    s.add(start >= arrival_at_pacific_heights)  # Cannot start before arriving at Pacific Heights
    s.add(start + min_duration <= barbara_available_end)  # Meeting must end by 10:00 PM
    
    # Minimize the start time to meet as early as possible
    s.minimize(start)
    
    if s.check() == sat:
        m = s.model()
        start_minutes = m.eval(start).as_long()
        end_minutes = start_minutes + min_duration
        
        # Convert minutes back to HH:MM format
        start_hour = start_minutes // 60
        start_minute = start_minutes % 60
        start_time = f"{start_hour:02d}:{start_minute:02d}"
        
        end_hour = end_minutes // 60
        end_minute = end_minutes % 60
        end_time = f"{end_hour:02d}:{end_minute:02d}"
        
        # Create the itinerary
        itinerary = [
            {"action": "meet", "person": "Barbara", "start_time": start_time, "end_time": end_time}
        ]
        
        # Output the result as JSON
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()