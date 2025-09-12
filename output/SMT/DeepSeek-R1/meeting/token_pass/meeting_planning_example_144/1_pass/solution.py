import json
from z3 import *

def min_to_time(minutes):
    total_minutes = 9 * 60 + minutes
    hours = total_minutes // 60
    minutes = total_minutes % 60
    return f"{hours}:{minutes:02}"

def main():
    # Define travel times (in minutes)
    travel_times = {
        ("The Castro", "Mission District"): 7,
        ("The Castro", "Financial District"): 20,
        ("Mission District", "The Castro"): 7,
        ("Mission District", "Financial District"): 17,
        ("Financial District", "The Castro"): 23,
        ("Financial District", "Mission District"): 17
    }

    # Convert availability times to minutes from 9:00
    laura_start = 12 * 60 + 15 - 9 * 60
    laura_end = 19 * 60 + 45 - 9 * 60
    anthony_start = 12 * 60 + 30 - 9 * 60
    anthony_end = 14 * 60 + 45 - 9 * 60

    # Meeting durations
    laura_duration = 75
    anthony_duration = 30

    # Try scheduling both meetings in different orders
    for order in [("Laura", "Anthony"), ("Anthony", "Laura")]:
        s = Solver()
        
        # Create variables for meeting start times
        meet1_start = Int(f"{order[0]}_start")
        meet2_start = Int(f"{order[1]}_start")
        
        # Create variables for travel times
        travel1 = Int("travel1")
        travel2 = Int("travel2")
        
        # Set travel times based on order
        if order[0] == "Laura":
            travel1 = travel_times[("The Castro", "Mission District")]
            travel2 = travel_times[("Mission District", "Financial District")]
        else:
            travel1 = travel_times[("The Castro", "Financial District")]
            travel2 = travel_times[("Financial District", "Mission District")]
        
        # Add constraints for first meeting
        if order[0] == "Laura":
            s.add(meet1_start >= laura_start)
            s.add(meet1_start + laura_duration <= laura_end)
        else:
            s.add(meet1_start >= anthony_start)
            s.add(meet1_start + anthony_duration <= anthony_end)
        
        # Add constraints for travel to first meeting
        s.add(meet1_start >= travel1)
        
        # Add constraints for second meeting
        if order[1] == "Laura":
            s.add(meet2_start >= laura_start)
            s.add(meet2_start + laura_duration <= laura_end)
        else:
            s.add(meet2_start >= anthony_start)
            s.add(meet2_start + anthony_duration <= anthony_end)
        
        # Add constraints for travel between meetings
        s.add(meet2_start >= meet1_start + (laura_duration if order[0] == "Laura" else anthony_duration) + travel2)
        
        if s.check() == sat:
            model = s.model()
            m1_start = model[meet1_start].as_long()
            m2_start = model[meet2_start].as_long()
            
            itinerary = []
            if order[0] == "Laura":
                itinerary.append({
                    "action": "meet",
                    "location": "Mission District",
                    "person": "Laura",
                    "start_time": min_to_time(m1_start),
                    "end_time": min_to_time(m1_start + laura_duration)
                })
            else:
                itinerary.append({
                    "action": "meet",
                    "location": "Financial District",
                    "person": "Anthony",
                    "start_time": min_to_time(m1_start),
                    "end_time": min_to_time(m1_start + anthony_duration)
                })
                
            if order[1] == "Laura":
                itinerary.append({
                    "action": "meet",
                    "location": "Mission District",
                    "person": "Laura",
                    "start_time": min_to_time(m2_start),
                    "end_time": min_to_time(m2_start + laura_duration)
                })
            else:
                itinerary.append({
                    "action": "meet",
                    "location": "Financial District",
                    "person": "Anthony",
                    "start_time": min_to_time(m2_start),
                    "end_time": min_to_time(m2_start + anthony_duration)
                })
            
            print(json.dumps({"itinerary": itinerary}, indent=2))
            return

    # If both orders fail, try meeting only Laura
    s = Solver()
    laura_start_time = Int("laura_start")
    s.add(laura_start_time >= laura_start)
    s.add(laura_start_time + laura_duration <= laura_end)
    s.add(laura_start_time >= travel_times[("The Castro", "Mission District")])
    
    if s.check() == sat:
        model = s.model()
        start_time = model[laura_start_time].as_long()
        itinerary = [{
            "action": "meet",
            "location": "Mission District",
            "person": "Laura",
            "start_time": min_to_time(start_time),
            "end_time": min_to_time(start_time + laura_duration)
        }]
        print(json.dumps({"itinerary": itinerary}, indent=2))
        return

    # Finally, try meeting only Anthony
    s = Solver()
    anthony_start_time = Int("anthony_start")
    s.add(anthony_start_time >= anthony_start)
    s.add(anthony_start_time + anthony_duration <= anthony_end)
    s.add(anthony_start_time >= travel_times[("The Castro", "Financial District")])
    
    if s.check() == sat:
        model = s.model()
        start_time = model[anthony_start_time].as_long()
        itinerary = [{
            "action": "meet",
            "location": "Financial District",
            "person": "Anthony",
            "start_time": min_to_time(start_time),
            "end_time": min_to_time(start_time + anthony_duration)
        }]
        print(json.dumps({"itinerary": itinerary}, indent=2))
        return

    # If no meetings are possible
    print('{"itinerary": []}')

if __name__ == "__main__":
    main()