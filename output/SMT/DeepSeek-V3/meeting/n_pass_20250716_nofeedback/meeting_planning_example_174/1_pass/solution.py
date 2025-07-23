from z3 import *
import datetime

def solve_scheduling():
    # Initialize Z3 solver
    s = Solver()

    # Define variables for meeting start and end times (in minutes since 9:00 AM)
    # Kenneth's meeting at Mission District
    k_start = Int('k_start')  # minutes from 9:00 AM
    k_end = Int('k_end')
    # Thomas's meeting at Pacific Heights
    t_start = Int('t_start')
    t_end = Int('t_end')

    # Convert friend availability to minutes since 9:00 AM
    # Kenneth available from 12:00 PM to 3:45 PM (180 to 405 minutes)
    k_available_start = (12 - 9) * 60  # 180 minutes
    k_available_end = (15 - 9) * 60 + 45  # 405 minutes
    # Thomas available from 3:30 PM to 7:15 PM (390 to 615 minutes)
    t_available_start = (15 - 9) * 60 + 30  # 390 minutes
    t_available_end = (19 - 9) * 60 + 15  # 615 minutes

    # Minimum durations in minutes
    k_min_duration = 45
    t_min_duration = 75

    # Constraints for Kenneth's meeting
    s.add(k_start >= k_available_start)
    s.add(k_end <= k_available_end)
    s.add(k_end - k_start >= k_min_duration)

    # Constraints for Thomas's meeting
    s.add(t_start >= t_available_start)
    s.add(t_end <= t_available_end)
    s.add(t_end - t_start >= t_min_duration)

    # Travel times between locations (in minutes)
    # Nob Hill to Mission District: 13
    # Mission District to Pacific Heights: 16
    # Nob Hill to Pacific Heights: 8
    # Pacific Heights to Mission District: 15

    # We start at Nob Hill at 0 minutes (9:00 AM)
    # Possible sequences:
    # Option 1: Meet Kenneth first, then Thomas
    #   - Travel Nob Hill to Mission District: 13 minutes
    #   - Meet Kenneth: k_start >= 13, k_end
    #   - Travel Mission District to Pacific Heights: 16 minutes
    #   - t_start >= k_end + 16
    # Option 2: Meet Thomas first, then Kenneth
    #   - Travel Nob Hill to Pacific Heights: 8 minutes
    #   - Meet Thomas: t_start >= 8, t_end
    #   - Travel Pacific Heights to Mission District: 15 minutes
    #   - k_start >= t_end + 15
    # But Kenneth's availability ends at 405 minutes, and Thomas starts at earliest 390.
    # So Option 2 is impossible because meeting Thomas first would require k_start >= t_end + 15 >= 390 + 75 + 15 = 480, but Kenneth's window ends at 405.
    # Thus, only Option 1 is feasible.

    # So, we model Option 1:
    s.add(k_start >= 13)  # travel to Mission District
    s.add(t_start >= k_end + 16)  # travel to Pacific Heights after meeting Kenneth

    # Ensure the schedule is feasible
    if s.check() == sat:
        m = s.model()
        k_start_val = m.evaluate(k_start).as_long()
        k_end_val = m.evaluate(k_end).as_long()
        t_start_val = m.evaluate(t_start).as_long()
        t_end_val = m.evaluate(t_end).as_long()

        # Convert minutes since 9:00 AM to HH:MM format
        def minutes_to_time(minutes):
            time = datetime.datetime(2023, 1, 1, 9, 0) + datetime.timedelta(minutes=minutes)
            return time.strftime("%H:%M")

        itinerary = [
            {"action": "meet", "person": "Kenneth", "start_time": minutes_to_time(k_start_val), "end_time": minutes_to_time(k_end_val)},
            {"action": "meet", "person": "Thomas", "start_time": minutes_to_time(t_start_val), "end_time": minutes_to_time(t_end_val)}
        ]
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

solution = solve_scheduling()
print("SOLUTION:")
print(solution)