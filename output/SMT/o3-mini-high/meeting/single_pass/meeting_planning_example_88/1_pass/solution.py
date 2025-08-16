import json
from z3 import Optimize, Int, sat

def format_time(minutes):
    hour = minutes // 60
    minute = minutes % 60
    return f"{hour:02d}:{minute:02d}"

def main():
    # Create an Optimize object from Z3
    opt = Optimize()
    
    # Define integer variables representing the meeting start and end times (in minutes from midnight)
    j_start = Int("j_start")
    j_end = Int("j_end")
    
    # Constants (in minutes from midnight)
    # 09:00 AM in minutes
    arrival_sunset = 9 * 60         # 540
    # Joshua is at Golden Gate Park from 20:45 to 21:45
    j_available_start = 20 * 60 + 45 # 1245
    j_available_end   = 21 * 60 + 45 # 1305
    # Travel times in minutes
    travel_to_park = 11
    
    # Add constraints:
    # 1. You must be able to depart from Sunset District (arrived at 09:00) and travel to Golden Gate Park.
    #    We require that you leave at (j_start - travel_time) but that must be after your arrival at Sunset.
    opt.add(j_start - travel_to_park >= arrival_sunset)
    
    # 2. Joshua is available from 20:45 (1245) to 21:45 (1305)
    opt.add(j_start >= j_available_start)
    opt.add(j_end <= j_available_end)
    
    # 3. The meeting with Joshua must last at least 15 minutes.
    opt.add(j_end - j_start >= 15)
    
    # Objective:
    # Since you want to meet as many friends as possible, in this simplified scenario with one friend,
    # it is beneficial to maximize your meeting time with Joshua (using his available window).
    # Therefore we maximize the meeting duration subject to the above constraints.
    opt.maximize(j_end - j_start)
    
    # Check for a solution
    if opt.check() == sat:
        model = opt.model()
        j_start_val = model[j_start].as_long()
        j_end_val = model[j_end].as_long()
        
        # Prepare the itinerary entry for meeting Joshua.
        itinerary = [
            {
                "action": "meet",
                "person": "Joshua",
                "start_time": format_time(j_start_val),
                "end_time": format_time(j_end_val)
            }
        ]
        output = {"itinerary": itinerary}
        print(json.dumps(output, indent=2))
    else:
        print("No solution found.")

if __name__ == "__main__":
    main()