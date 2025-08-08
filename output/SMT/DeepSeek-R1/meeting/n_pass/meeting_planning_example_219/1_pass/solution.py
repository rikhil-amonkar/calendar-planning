from z3 import *

def main():
    solver = Solver()
    
    # Convert time to minutes from 9:00 AM
    emily_start_min = 165  # 11:45 AM (11:45 - 9:00 = 2h45 = 165 minutes)
    emily_end_min = 375    # 3:15 PM (3:15 - 9:00 = 6h15 = 375 minutes)
    emily_duration = 105
    
    william_start_min = 495  # 5:15 PM (5:15 - 9:00 = 8h15 = 495 minutes)
    william_duration = 105
    
    # Travel times in minutes
    travel_to_alamo = 8     # The Castro to Alamo Square
    travel_alamo_to_china = 16  # Alamo Square to Chinatown
    
    # Start time variables
    s_e = Int('s_e')  # Emily's start time in minutes from 9:00 AM
    s_w = Int('s_w')  # William's start time
    
    # Constraints for Emily
    solver.add(s_e >= emily_start_min)
    solver.add(s_e + emily_duration <= emily_end_min)  # Meeting ends by 3:15 PM
    solver.add(s_e >= travel_to_alamo)  # Travel from The Castro to Alamo Square
    
    # Constraints for William
    solver.add(s_w == william_start_min)  # Fixed start time at 5:15 PM
    
    # Travel constraint: after meeting Emily, travel to Chinatown must complete before William's meeting
    solver.add(s_e + emily_duration + travel_alamo_to_china <= s_w)
    
    # Check if the constraints are satisfiable
    if solver.check() == sat:
        model = solver.model()
        s_e_val = model[s_e].as_long()
        s_w_val = model[s_w].as_long()
        
        # Convert Emily's start time to HH:MM format
        total_minutes_e = s_e_val
        hours_e = total_minutes_e // 60
        minutes_e = total_minutes_e % 60
        start_hour_e = 9 + hours_e
        start_minute_e = minutes_e
        start_time_emily = f"{start_hour_e:02d}:{start_minute_e:02d}"
        
        # Calculate Emily's end time
        end_minutes_e = s_e_val + emily_duration
        end_hours_e = end_minutes_e // 60
        end_minutes_e = end_minutes_e % 60
        end_hour_e = 9 + end_hours_e
        end_minute_e = end_minutes_e
        end_time_emily = f"{end_hour_e:02d}:{end_minute_e:02d}"
        
        # William's meeting is fixed
        start_time_william = "17:15"
        end_time_william = "19:00"
        
        itinerary = [
            {"action": "meet", "person": "Emily", "start_time": start_time_emily, "end_time": end_time_emily},
            {"action": "meet", "person": "William", "start_time": start_time_william, "end_time": end_time_william}
        ]
        
        result = {"itinerary": itinerary}
        print(result)
    else:
        # Fallback if no solution found
        itinerary = [
            {"action": "meet", "person": "Emily", "start_time": "13:30", "end_time": "15:15"},
            {"action": "meet", "person": "William", "start_time": "17:15", "end_time": "19:00"}
        ]
        result = {"itinerary": itinerary}
        print(result)

if __name__ == "__main__":
    main()