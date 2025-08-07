from z3 import *

def solve_scheduling():
    # Initialize Z3 solver
    s = Solver()

    # Convert all times to minutes since midnight for easier calculations
    base_time = 9 * 60  # 9:00 AM in minutes since midnight

    # Define variables for meeting start and end times in minutes since midnight
    k_start = Int('k_start')  # Kenneth's meeting start time
    k_end = Int('k_end')      # Kenneth's meeting end time
    t_start = Int('t_start')  # Thomas's meeting start time
    t_end = Int('t_end')      # Thomas's meeting end time

    # Convert friends' available times to minutes since midnight
    # Kenneth available from 12:00 PM (720) to 3:45 PM (945)
    k_available_start = 12 * 60
    k_available_end = 15 * 60 + 45

    # Thomas available from 3:30 PM (990) to 7:15 PM (1155)
    t_available_start = 15 * 60 + 30
    t_available_end = 19 * 60 + 15

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
    # From Nob Hill to Pacific Heights: 8 minutes (alternative if meeting Thomas first)

    # We start at Nob Hill at 9:00 AM (540 minutes since midnight)
    # Option 1: Meet Kenneth first, then Thomas
    # Time to travel to Mission District: 13 minutes
    s.add(k_start >= base_time + 13)  # can't meet Kenneth before arriving at Mission District at 9:00 AM + 13 minutes

    # Time to travel from Mission District to Pacific Heights after meeting Kenneth: 16 minutes
    s.add(t_start >= k_end + 16)

    # Option 2: Meet Thomas first, then Kenneth
    # Time to travel to Pacific Heights: 8 minutes
    # s.add(t_start >= base_time + 8)
    # Time to travel from Pacific Heights to Mission District: 15 minutes
    # s.add(k_start >= t_end + 15)
    # But Thomas's window starts at 3:30 PM, which is after Kenneth's window ends at 3:45 PM, so this option is not feasible

    # Check if the solver can find a solution
    if s.check() == sat:
        m = s.model()
        # Get the meeting times in minutes since midnight
        k_start_val = m.evaluate(k_start).as_long()
        k_end_val = m.evaluate(k_end).as_long()
        t_start_val = m.evaluate(t_start).as_long()
        t_end_val = m.evaluate(t_end).as_long()

        # Convert back to HH:MM format
        def to_time_str(minutes):
            hours = minutes // 60
            mins = minutes % 60
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