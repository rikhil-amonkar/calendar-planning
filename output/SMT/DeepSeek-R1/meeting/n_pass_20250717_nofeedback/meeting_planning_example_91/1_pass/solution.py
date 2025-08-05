from z3 import *
import json

def main():
    s = Solver()
    
    # Define the start time of meeting Daniel (in minutes from midnight)
    start_daniel = Int('start_daniel')
    
    # Daniel's availability: 19:00 (1140 minutes) to 20:15 (1215 minutes)
    s.add(start_daniel >= 1140)  # Meeting must start at or after 19:00
    s.add(start_daniel + 75 <= 1215)  # Meeting must end by 20:15 and last at least 75 minutes
    
    # Travel constraint: Leave Russian Hill at start_daniel - 14 minutes, which must be after 9:00 (540 minutes)
    s.add(start_daniel - 14 >= 540)
    
    # Check for a solution
    if s.check() == sat:
        model = s.model()
        start_val = model.eval(start_daniel).as_long()
        end_val = start_val + 75
        
        # Format start and end times as HH:MM
        start_hour = start_val // 60
        start_min = start_val % 60
        end_hour = end_val // 60
        end_min = end_val % 60
        
        start_time = f"{start_hour:02d}:{start_min:02d}"
        end_time = f"{end_hour:02d}:{end_min:02d}"
        
        # Create the itinerary
        itinerary = [{
            "action": "meet",
            "person": "Daniel",
            "start_time": start_time,
            "end_time": end_time
        }]
        
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()