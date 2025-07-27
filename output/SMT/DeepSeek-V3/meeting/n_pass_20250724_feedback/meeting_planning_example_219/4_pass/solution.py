from z3 import *
import json

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Define variables for meeting start and end times (in minutes since midnight)
    emily_start = Int('emily_start')
    emily_end = Int('emily_end')
    barbara_start = Int('barbara_start')
    barbara_end = Int('barbara_end')
    william_start = Int('william_start')
    william_end = Int('william_end')

    # Define travel times (in minutes)
    travel_castro_to_alamo = 8
    travel_alamo_to_union = 14
    travel_union_to_china = 7

    # Convert time windows to minutes since midnight
    emily_window_start = 11 * 60 + 45  # 11:45 AM
    emily_window_end = 15 * 60 + 15    # 3:15 PM
    barbara_window_start = 16 * 60 + 45  # 4:45 PM
    barbara_window_end = 18 * 60 + 15   # 6:15 PM
    william_window_start = 17 * 60 + 15  # 5:15 PM
    william_window_end = 19 * 60 + 0    # 7:00 PM

    # Starting time at The Castro (9:00 AM)
    start_time = 9 * 60

    # Constraints for Emily
    s.add(emily_start >= emily_window_start)
    s.add(emily_end <= emily_window_end)
    s.add(emily_end - emily_start >= 105)  # Minimum 105 minutes

    # Constraints for Barbara
    s.add(barbara_start >= barbara_window_start)
    s.add(barbara_end <= barbara_window_end)
    s.add(barbara_end - barbara_start >= 60)  # Minimum 60 minutes

    # Constraints for William
    s.add(william_start >= william_window_start)
    s.add(william_end <= william_window_end)
    s.add(william_end - william_start >= 105)  # Minimum 105 minutes

    # Travel constraints
    # From The Castro to Alamo Square
    s.add(emily_start >= start_time + travel_castro_to_alamo)
    
    # From Alamo Square to Union Square
    s.add(barbara_start >= emily_end + travel_alamo_to_union)
    
    # From Union Square to Chinatown
    s.add(william_start >= barbara_end + travel_union_to_china)

    # Check if all constraints can be satisfied
    if s.check() == sat:
        model = s.model()
        # Convert model times back to HH:MM format
        def minutes_to_time(minutes):
            h = minutes // 60
            m = minutes % 60
            return f"{h:02d}:{m:02d}"

        emily_s = model[emily_start].as_long()
        emily_e = model[emily_end].as_long()
        barbara_s = model[barbara_start].as_long()
        barbara_e = model[barbara_end].as_long()
        william_s = model[william_start].as_long()
        william_e = model[william_end].as_long()

        itinerary = [
            {"action": "meet", "person": "Emily", "start_time": minutes_to_time(emily_s), "end_time": minutes_to_time(emily_e)},
            {"action": "meet", "person": "Barbara", "start_time": minutes_to_time(barbara_s), "end_time": minutes_to_time(barbara_e)},
            {"action": "meet", "person": "William", "start_time": minutes_to_time(william_s), "end_time": minutes_to_time(william_e)}
        ]
        return {"itinerary": itinerary}
    else:
        return {"error": "No feasible schedule found."}

result = solve_scheduling()
print(json.dumps(result, indent=2))