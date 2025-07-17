from z3 import *
import json

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Define variables for each meeting's start and end times (in minutes since 9:00 AM)
    # Convert all times to minutes from 9:00 AM (540 minutes since midnight)
    timothy_start = Int('timothy_start')
    timothy_end = Int('timothy_end')
    mark_start = Int('mark_start')
    mark_end = Int('mark_end')
    joseph_start = Int('joseph_start')
    joseph_end = Int('joseph_end')

    # Convert all given times to minutes since 9:00 AM (0)
    # Timothy: 12:00 PM to 4:15 PM (180 to 435 minutes from 9:00 AM)
    timothy_window_start = (12 - 9) * 60  # 180
    timothy_window_end = (16 + 15/60 - 9) * 60  # 435
    # Mark: 6:45 PM to 9:00 PM (1170 - 540 = 630 to 1260 - 540 = 720 minutes from 9:00 AM)
    mark_window_start = (18 + 45/60 - 9) * 60  # 585
    mark_window_end = (21 - 9) * 60  # 720
    # Joseph: 4:45 PM to 9:30 PM (16.75 - 9)*60 = 465 to (21.5 -9)*60 = 750 minutes from 9:00 AM
    joseph_window_start = (16 + 45/60 - 9) * 60  # 465
    joseph_window_end = (21 + 30/60 - 9) * 60  # 750

    # Add constraints for each meeting
    # Timothy must be at least 105 minutes
    s.add(timothy_start >= timothy_window_start)
    s.add(timothy_end <= timothy_window_end)
    s.add(timothy_end - timothy_start >= 105)

    # Mark must be at least 60 minutes
    s.add(mark_start >= mark_window_start)
    s.add(mark_end <= mark_window_end)
    s.add(mark_end - mark_start >= 60)

    # Joseph must be at least 60 minutes
    s.add(joseph_start >= joseph_window_start)
    s.add(joseph_end <= joseph_window_end)
    s.add(joseph_end - joseph_start >= 60)

    # Initial location: Golden Gate Park at time 0 (9:00 AM)
    # Assume the first activity is meeting Timothy at Alamo Square.
    # Travel from Golden Gate Park to Alamo Square takes 10 minutes.
    # So, the earliest Timothy can be met is 10 minutes after 9:00 AM (10 minutes from start).
    # But Timothy is only available from 12:00 PM (180 minutes), so this is already handled by the window.

    # Now, we need to sequence the meetings with travel times.
    # Possible orders: Timothy -> Joseph -> Mark, or Timothy -> Mark -> Joseph, etc.
    # We'll model the possible orders and let Z3 find a feasible solution.

    # Let's assume the order is Timothy -> Joseph -> Mark.
    # Then:
    # After meeting Timothy at Alamo Square, travel to Joseph's location (Russian Hill) takes 13 minutes.
    s.add(joseph_start >= timothy_end + 13)
    # After meeting Joseph, travel to Mark's location (Presidio) takes 14 minutes.
    s.add(mark_start >= joseph_end + 14)

    # Alternatively, the order could be Timothy -> Mark -> Joseph.
    # Then:
    # After meeting Timothy, travel to Mark's location (Presidio) takes 18 minutes.
    # s.add(mark_start >= timothy_end + 18)
    # After meeting Mark, travel to Joseph's location (Russian Hill) takes 14 minutes.
    # s.add(joseph_start >= mark_end + 14)

    # But to model all possible orders, we can use auxiliary variables to represent the order.
    # However, for simplicity, we'll proceed with the first order (Timothy -> Joseph -> Mark) and check if it's feasible.
    # If not, we can try other orders.

    # Check if the current model is satisfiable
    if s.check() == sat:
        m = s.model()
        # Convert times back to HH:MM format
        def minutes_to_time(minutes):
            total_minutes = 540 + minutes  # 9:00 AM is 540 minutes
            hours = total_minutes // 60
            mins = total_minutes % 60
            return f"{int(hours):02d}:{int(mins):02d}"

        timothy_s = m.eval(timothy_start).as_long()
        timothy_e = m.eval(timothy_end).as_long()
        joseph_s = m.eval(joseph_start).as_long()
        joseph_e = m.eval(joseph_end).as_long()
        mark_s = m.eval(mark_start).as_long()
        mark_e = m.eval(mark_end).as_long()

        itinerary = [
            {"action": "meet", "person": "Timothy", "start_time": minutes_to_time(timothy_s), "end_time": minutes_to_time(timothy_e)},
            {"action": "meet", "person": "Joseph", "start_time": minutes_to_time(joseph_s), "end_time": minutes_to_time(joseph_e)},
            {"action": "meet", "person": "Mark", "start_time": minutes_to_time(mark_s), "end_time": minutes_to_time(mark_e)}
        ]
        return {"itinerary": itinerary}
    else:
        # Try a different order: Timothy -> Mark -> Joseph
        s = Solver()
        timothy_start = Int('timothy_start')
        timothy_end = Int('timothy_end')
        mark_start = Int('mark_start')
        mark_end = Int('mark_end')
        joseph_start = Int('joseph_start')
        joseph_end = Int('joseph_end')

        # Add time window constraints
        s.add(timothy_start >= timothy_window_start)
        s.add(timothy_end <= timothy_window_end)
        s.add(timothy_end - timothy_start >= 105)

        s.add(mark_start >= mark_window_start)
        s.add(mark_end <= mark_window_end)
        s.add(mark_end - mark_start >= 60)

        s.add(joseph_start >= joseph_window_start)
        s.add(joseph_end <= joseph_window_end)
        s.add(joseph_end - joseph_start >= 60)

        # Order: Timothy -> Mark -> Joseph
        s.add(mark_start >= timothy_end + 18)  # Alamo Square to Presidio: 18 minutes
        s.add(joseph_start >= mark_end + 14)   # Presidio to Russian Hill: 14 minutes

        if s.check() == sat:
            m = s.model()
            def minutes_to_time(minutes):
                total_minutes = 540 + minutes
                hours = total_minutes // 60
                mins = total_minutes % 60
                return f"{int(hours):02d}:{int(mins):02d}"

            timothy_s = m.eval(timothy_start).as_long()
            timothy_e = m.eval(timothy_end).as_long()
            mark_s = m.eval(mark_start).as_long()
            mark_e = m.eval(mark_end).as_long()
            joseph_s = m.eval(joseph_start).as_long()
            joseph_e = m.eval(joseph_end).as_long()

            itinerary = [
                {"action": "meet", "person": "Timothy", "start_time": minutes_to_time(timothy_s), "end_time": minutes_to_time(timothy_e)},
                {"action": "meet", "person": "Mark", "start_time": minutes_to_time(mark_s), "end_time": minutes_to_time(mark_e)},
                {"action": "meet", "person": "Joseph", "start_time": minutes_to_time(joseph_s), "end_time": minutes_to_time(joseph_e)}
            ]
            return {"itinerary": itinerary}
        else:
            return {"itinerary": []}

result = solve_scheduling()
print(json.dumps(result, indent=2))