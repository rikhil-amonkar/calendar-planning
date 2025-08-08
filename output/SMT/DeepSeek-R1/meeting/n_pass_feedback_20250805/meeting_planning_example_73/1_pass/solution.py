from z3 import *
import json

def main():
    # Initialize the optimizer
    s = Optimize()
    # Define the start time in minutes after 9:00 AM
    start = Int('start')

    # Add constraints
    # 1. Travel time to Pacific Heights is 7 minutes, so start time must be at least 7
    # 2. Meeting must end by 10:00 PM (780 minutes after 9:00 AM) and lasts 60 minutes
    s.add(start >= 7)
    s.add(start + 60 <= 780)

    # Minimize the start time to meet as early as possible
    s.minimize(start)

    if s.check() == sat:
        model = s.model()
        start_val = model[start].as_long()
        
        # Calculate start time (HH:MM)
        total_minutes_start = start_val
        hours_start = 9 + total_minutes_start // 60
        minutes_start = total_minutes_start % 60
        start_time = f"{hours_start:02d}:{minutes_start:02d}"
        
        # Calculate end time (start + 60 minutes)
        end_val = start_val + 60
        hours_end = 9 + end_val // 60
        minutes_end = end_val % 60
        end_time = f"{hours_end:02d}:{minutes_end:02d}"
        
        # Create itinerary
        itinerary = [{
            "action": "meet",
            "person": "Barbara",
            "start_time": start_time,
            "end_time": end_time
        }]
        
        # Output as JSON
        print(json.dumps({"itinerary": itinerary}))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()