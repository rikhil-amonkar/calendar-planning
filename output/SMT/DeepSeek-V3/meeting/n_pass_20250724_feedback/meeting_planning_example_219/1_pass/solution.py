from z3 import *
import json

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Define variables for meeting start and end times
    # Meeting with Emily at Alamo Square
    emily_start = Int('emily_start')
    emily_end = Int('emily_end')
    # Meeting with Barbara at Union Square
    barbara_start = Int('barbara_start')
    barbara_end = Int('barbara_end')
    # Meeting with William at Chinatown
    william_start = Int('william_start')
    william_end = Int('william_end')

    # Define variables for travel times
    # Time to leave The Castro (starting point) to Alamo Square (Emily)
    leave_castro_to_alamo = Int('leave_castro_to_alamo')
    # Time to leave Alamo Square to Union Square (Barbara)
    leave_alamo_to_union = Int('leave_alamo_to_union')
    # Time to leave Union Square to Chinatown (William)
    leave_union_to_china = Int('leave_union_to_china')

    # Convert all times to minutes since 9:00 AM (540 minutes)
    emily_window_start = 11 * 60 + 45  # 11:45 AM
    emily_window_end = 15 * 60 + 15    # 3:15 PM
    barbara_window_start = 16 * 60 + 45 # 4:45 PM
    barbara_window_end = 18 * 60 + 15   # 6:15 PM
    william_window_start = 17 * 60 + 15 # 5:15 PM
    william_window_end = 19 * 60 + 0    # 7:00 PM

    # Constraints for Emily
    s.add(emily_start >= emily_window_start)
    s.add(emily_end <= emily_window_end)
    s.add(emily_end - emily_start >= 105)  # 105 minutes

    # Constraints for Barbara
    s.add(barbara_start >= barbara_window_start)
    s.add(barbara_end <= barbara_window_end)
    s.add(barbara_end - barbara_start >= 60)  # 60 minutes

    # Constraints for William
    s.add(william_start >= william_window_start)
    s.add(william_end <= william_window_end)
    s.add(william_end - william_start >= 105)  # 105 minutes

    # Initial departure from The Castro to Alamo Square
    s.add(leave_castro_to_alamo >= 540)  # 9:00 AM is 540 minutes
    # Arrive at Alamo Square by emily_start
    s.add(emily_start >= leave_castro_to_alamo + 8)  # travel time 8 minutes

    # Depart from Alamo Square to Union Square
    s.add(leave_alamo_to_union >= emily_end)
    # Arrive at Union Square by barbara_start
    s.add(barbara_start >= leave_alamo_to_union + 14)  # travel time 14 minutes

    # Depart from Union Square to Chinatown
    s.add(leave_union_to_china >= barbara_end)
    # Arrive at Chinatown by william_start
    s.add(william_start >= leave_union_to_china + 7)  # travel time 7 minutes

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