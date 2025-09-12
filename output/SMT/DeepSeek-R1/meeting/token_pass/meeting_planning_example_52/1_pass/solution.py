from z3 import *
import json

def main():
    # Convert all times to minutes since 9:00 AM (540 minutes since midnight)
    base_time = 9 * 60  # 9:00 AM in minutes since midnight
    
    # Barbara's availability in minutes since base (9:00 AM)
    barbara_start = (13 * 60 + 15) - base_time  # 1:15 PM -> 255 minutes
    barbara_end = (18 * 60 + 15) - base_time    # 6:15 PM -> 555 minutes
    
    # Travel times in minutes
    travel_to_richmond = 14
    travel_to_russian = 13
    
    # Meeting duration constraint
    min_meeting_duration = 45
    
    # Z3 variables
    departure_time = Int('departure_time')  # When we leave Russian Hill
    meeting_start = Int('meeting_start')    # When meeting with Barbara starts
    meeting_end = Int('meeting_end')        # When meeting with Barbara ends
    
    # Create solver with optimization
    opt = Optimize()
    
    # Constraints
    opt.add(departure_time >= 0)  # Can't leave before 9:00 AM
    opt.add(meeting_start >= barbara_start)
    opt.add(meeting_end <= barbara_end)
    opt.add(meeting_end - meeting_start >= min_meeting_duration)
    
    # Travel constraints: arrive at Richmond after travel time
    arrival_time = departure_time + travel_to_richmond
    opt.add(meeting_start >= arrival_time)
    
    # Return travel constraint (optional but included for completeness)
    # opt.add(return_time >= meeting_end + travel_to_russian)
    
    # Maximize the meeting duration or minimize waiting time
    # Here we maximize the meeting start time to meet as late as possible
    opt.maximize(meeting_start)
    
    # Check feasibility
    if opt.check() == sat:
        m = opt.model()
        dep_time = m.evaluate(departure_time).as_long()
        start_time = m.evaluate(meeting_start).as_long()
        end_time = m.evaluate(meeting_end).as_long()
        
        # Convert back to human-readable times
        def format_time(minutes):
            total_minutes = base_time + minutes
            hours = total_minutes // 60
            mins = total_minutes % 60
            return f"{hours}:{mins:02d}"
        
        # Create itinerary
        itinerary = [
            {
                "action": "meet",
                "location": "Richmond District",
                "person": "Barbara",
                "start_time": format_time(start_time),
                "end_time": format_time(end_time)
            }
        ]
        
        print(json.dumps({"itinerary": itinerary}, indent=2))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()