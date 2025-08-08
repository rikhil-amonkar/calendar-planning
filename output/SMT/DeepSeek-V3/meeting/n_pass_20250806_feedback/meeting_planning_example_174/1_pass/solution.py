from z3 import *
import datetime

def solve_scheduling():
    # Initialize Z3 solver
    s = Solver()

    # Convert all times to minutes since 9:00 AM (540 minutes)
    base_time = 9 * 60  # 9:00 AM in minutes

    # Define variables for meeting start and end times in minutes since base_time
    # Meeting Kenneth (Mission District)
    k_start = Int('k_start')
    k_end = Int('k_end')
    # Meeting Thomas (Pacific Heights)
    t_start = Int('t_start')
    t_end = Int('t_end')

    # Convert friends' available times to minutes since base_time
    # Kenneth available from 12:00 PM (720) to 3:45 PM (945) in absolute minutes
    k_available_start = 12 * 60 - base_time  # 180 minutes after 9:00 AM
    k_available_end = 15 * 45 - base_time    # 405 minutes after 9:00 AM (3:45 PM is 15*60 +45= 945; 945-540=405)

    # Thomas available from 3:30 PM (990) to 7:15 PM (1155) in absolute minutes
    t_available_start = 15 * 60 + 30 - base_time  # 390 minutes after 9:00 AM (3:30 PM is 15*60+30=930; 930-540=390)
    t_available_end = 19 * 60 + 15 - base_time    # 615 minutes after 9:00 AM (7:15 PM is 19*60+15=1155; 1155-540=615)

    # Add constraints for Kenneth's meeting
    s.add(k_start >= k_available_start)
    s.add(k_end <= k_available_end)
    s.add(k_end - k_start >= 45)  # at least 45 minutes

    # Add constraints for Thomas's meeting
    s.add(t_start >= t_available_start)
    s.add(t_end <= t_available_end)
    s.add(t_end - t_start >= 75)  # at least 75 minutes

    # Travel times (in minutes)
    # From Nob Hill to Mission District: 13 minutes (to meet Kenneth)
    # From Mission District to Pacific Heights: 16 minutes (to meet Thomas after Kenneth)
    # Or alternative: meet Thomas first, then Kenneth (but Thomas's window is later, so likely not possible)

    # We start at Nob Hill at time 0 (9:00 AM)
    # Option 1: Meet Kenneth first, then Thomas
    # Time to travel to Mission District: 13 minutes
    s.add(k_start >= 13)  # can't meet Kenneth before arriving at Mission District at 0 +13 minutes

    # Time to travel from Mission District to Pacific Heights after meeting Kenneth: 16 minutes
    s.add(t_start >= k_end + 16)

    # Check if the solver can find a solution
    if s.check() == sat:
        m = s.model()
        # Get the meeting times in minutes since base_time
        k_start_val = m.evaluate(k_start).as_long()
        k_end_val = m.evaluate(k_end).as_long()
        t_start_val = m.evaluate(t_start).as_long()
        t_end_val = m.evaluate(t_end).as_long()

        # Convert back to absolute times (from 9:00 AM)
        def to_time_str(minutes):
            total_minutes = base_time + minutes
            hours = total_minutes // 60
            mins = total_minutes % 60
            return f"{hours:02d}:{mins:02d}"

        k_start_time = to_time_str(k_start_val)
        k_end_time = to_time_str(k_end_val)
        t_start_time = to_time_str(t_start_val)
        t_end_time = to_time_str(t_end_val)

        itinerary = [
            {"action": "meet", "person": "Kenneth", "start_time": k_start_time, "end_time": k_end_time},
            {"action": "meet", "person": "Thomas", "start_time": t_start_time, "end_time": t_end_time}
        ]
        return {"itinerary": itinerary}
    else:
        return {"error": "No feasible schedule found"}

# Solve and print the solution
solution = solve_scheduling()
print(solution)