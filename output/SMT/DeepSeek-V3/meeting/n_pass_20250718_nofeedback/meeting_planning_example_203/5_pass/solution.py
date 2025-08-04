from z3 import *

def solve_scheduling_problem():
    # Initialize Z3 solver
    s = Solver()

    # Define time variables for each meeting (in minutes since midnight)
    timothy_start = Int('timothy_start')
    timothy_end = Int('timothy_end')
    david_start = Int('david_start')
    david_end = Int('david_end')
    robert_start = Int('robert_start')
    robert_end = Int('robert_end')

    # Arrival time at Financial District (9:00 AM in minutes since midnight)
    arrival_time = 540

    # Friends' availability windows in minutes since midnight
    david_available_start = 645  # 10:45 AM
    david_available_end = 930    # 3:30 PM
    timothy_available_start = 540 # 9:00 AM
    timothy_available_end = 930   # 3:30 PM
    robert_available_start = 735  # 12:15 PM
    robert_available_end = 1185   # 7:45 PM

    # Minimum meeting durations in minutes
    david_min_duration = 15
    timothy_min_duration = 75
    robert_min_duration = 90

    # Travel times between locations in minutes
    fd_to_ph = 13  # Financial District to Pacific Heights
    ph_to_fw = 13  # Pacific Heights to Fisherman's Wharf
    fw_to_md = 22  # Fisherman's Wharf to Mission District

    # Constraints for each meeting
    # Timothy meeting constraints
    s.add(timothy_start >= timothy_available_start)
    s.add(timothy_end <= timothy_available_end)
    s.add(timothy_end - timothy_start >= timothy_min_duration)

    # David meeting constraints
    s.add(david_start >= david_available_start)
    s.add(david_end <= david_available_end)
    s.add(david_end - david_start >= david_min_duration)

    # Robert meeting constraints
    s.add(robert_start >= robert_available_start)
    s.add(robert_end <= robert_available_end)
    s.add(robert_end - robert_start >= robert_min_duration)

    # Sequence constraints (order of meetings and travel times)
    # Start with Timothy at Pacific Heights
    s.add(timothy_start >= arrival_time + fd_to_ph)

    # After meeting Timothy, travel to Fisherman's Wharf to meet David
    s.add(david_start >= timothy_end + ph_to_fw)

    # After meeting David, travel to Mission District to meet Robert
    s.add(robert_start >= david_end + fw_to_md)

    # Additional constraints to ensure proper timing
    # David must start after his available start time
    s.add(david_start >= david_available_start)
    # Robert must start after his available start time
    s.add(robert_start >= robert_available_start)

    # Check if the solver can find a solution
    if s.check() == sat:
        model = s.model()
        # Convert times back to HH:MM format
        def minutes_to_time(minutes):
            hours = minutes // 60
            mins = minutes % 60
            return f"{hours:02d}:{mins:02d}"

        timothy_start_time = model.evaluate(timothy_start).as_long()
        timothy_end_time = model.evaluate(timothy_end).as_long()
        david_start_time = model.evaluate(david_start).as_long()
        david_end_time = model.evaluate(david_end).as_long()
        robert_start_time = model.evaluate(robert_start).as_long()
        robert_end_time = model.evaluate(robert_end).as_long()

        itinerary = [
            {"action": "meet", "person": "Timothy", "start_time": minutes_to_time(timothy_start_time), "end_time": minutes_to_time(timothy_end_time)},
            {"action": "meet", "person": "David", "start_time": minutes_to_time(david_start_time), "end_time": minutes_to_time(david_end_time)},
            {"action": "meet", "person": "Robert", "start_time": minutes_to_time(robert_start_time), "end_time": minutes_to_time(robert_end_time)}
        ]
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Solve the problem and print the result
result = solve_scheduling_problem()
print(result)