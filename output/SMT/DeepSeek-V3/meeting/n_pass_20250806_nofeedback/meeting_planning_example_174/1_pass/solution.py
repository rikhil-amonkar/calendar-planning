from z3 import *

def solve_scheduling():
    # Initialize Z3 solver
    s = Solver()

    # Define variables for meeting start and end times
    # Meeting Kenneth at Mission District
    kenneth_start = Int('kenneth_start')
    kenneth_end = Int('kenneth_end')

    # Meeting Thomas at Pacific Heights
    thomas_start = Int('thomas_start')
    thomas_end = Int('thomas_end')

    # Convert all times to minutes since 9:00 AM (540 minutes)
    # Kenneth's availability: 12:00 PM (720) to 3:45 PM (945)
    kenneth_available_start = 720  # 12:00 PM
    kenneth_available_end = 945    # 3:45 PM

    # Thomas's availability: 3:30 PM (1050) to 7:15 PM (1275)
    thomas_available_start = 1050  # 3:30 PM
    thomas_available_end = 1275    # 7:15 PM

    # Minimum meeting durations
    kenneth_min_duration = 45
    thomas_min_duration = 75

    # Travel times in minutes
    # Initial location: Nob Hill at 9:00 AM (540)
    # Travel from Nob Hill to Mission District: 13
    # Travel from Mission District to Pacific Heights: 16
    # Travel from Nob Hill to Pacific Heights: 8

    # Constraints for Kenneth's meeting
    s.add(kenneth_start >= kenneth_available_start)
    s.add(kenneth_end <= kenneth_available_end)
    s.add(kenneth_end - kenneth_start >= kenneth_min_duration)

    # Constraints for Thomas's meeting
    s.add(thomas_start >= thomas_available_start)
    s.add(thomas_end <= thomas_available_end)
    s.add(thomas_end - thomas_start >= thomas_min_duration)

    # Possible scenarios:
    # Option 1: Meet Kenneth first, then travel to Thomas
    # Option 2: Meet Thomas first (but he's only available after 3:30 PM, and Kenneth is available until 3:45 PM, so this is impossible)
    # So, only Option 1 is feasible.

    # Scenario: Start at Nob Hill, travel to Mission District (13 minutes), meet Kenneth, then travel to Pacific Heights (16 minutes), meet Thomas.
    # Arrival at Mission District: 540 + 13 = 553 (9:13 AM)
    # Kenneth's meeting must start no earlier than 12:00 PM (720)
    # So, wait from 9:13 AM to 12:00 PM (553 to 720) before meeting Kenneth.
    # Meet Kenneth from 12:00 PM to at least 12:45 PM (720 to 765)
    # Then travel to Pacific Heights: 16 minutes, arriving at 765 + 16 = 781 (1:01 PM)
    # Thomas is available from 3:30 PM (1050), so wait until 3:30 PM (1050)
    # Meet Thomas from 3:30 PM to at least 4:45 PM (1050 + 75 = 1125)

    # Alternatively, meet Kenneth later to minimize waiting time before Thomas.
    # For example, meet Kenneth from 2:00 PM to 2:45 PM (840 to 885), travel to Pacific Heights by 885 + 16 = 901 (3:01 PM), wait until 3:30 PM (1050), meet Thomas from 3:30 PM to 4:45 PM (1050 to 1125).

    # We'll let Z3 find a feasible solution.

    # Constraints for travel:
    # Initial travel to Mission District: 13 minutes, arriving at 540 + 13 = 553.
    # After meeting Kenneth, travel to Pacific Heights: 16 minutes.
    # So, thomas_start >= kenneth_end + 16
    s.add(thomas_start >= kenneth_end + 16)

    # Also, kenneth_start >= 540 + 13 (since we start at Nob Hill at 540)
    s.add(kenneth_start >= 540 + 13)

    # Check if the solver can find a solution
    if s.check() == sat:
        m = s.model()
        k_start = m.evaluate(kenneth_start).as_long()
        k_end = m.evaluate(kenneth_end).as_long()
        t_start = m.evaluate(thomas_start).as_long()
        t_end = m.evaluate(thomas_end).as_long()

        # Convert minutes back to HH:MM format
        def minutes_to_time(minutes):
            hours = minutes // 60
            mins = minutes % 60
            return f"{hours:02d}:{mins:02d}"

        itinerary = [
            {"action": "meet", "person": "Kenneth", "start_time": minutes_to_time(k_start), "end_time": minutes_to_time(k_end)},
            {"action": "meet", "person": "Thomas", "start_time": minutes_to_time(t_start), "end_time": minutes_to_time(t_end)}
        ]

        # Return the itinerary
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Execute the solver
result = solve_scheduling()
print(result)