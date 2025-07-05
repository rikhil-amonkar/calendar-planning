from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Define variables for meeting start and end times
    # Helen at North Beach
    helen_start = Int('helen_start')  # in minutes since 9:00 AM
    helen_end = Int('helen_end')
    
    # Kimberly at Fisherman's Wharf
    kimberly_start = Int('kimberly_start')
    kimberly_end = Int('kimberly_end')
    
    # Patricia at Bayview
    patricia_start = Int('patricia_start')
    patricia_end = Int('patricia_end')

    # Travel times (in minutes)
    # From Nob Hill to North Beach: 8 minutes
    # From North Beach to Fisherman's Wharf: 5 minutes
    # From Fisherman's Wharf to Bayview: 26 minutes

    # Convert friends' availability windows to minutes since 9:00 AM
    # Helen: 7:00 AM to 4:45 PM
    # Since we start at 9:00 AM, Helen's window is from -120 to 465 minutes (since 7:00 AM is 2 hours before 9:00 AM)
    helen_available_start = -120  # 7:00 AM is 120 minutes before 9:00 AM
    helen_available_end = 465      # 4:45 PM is 7 hours and 45 minutes after 9:00 AM (7*60 + 45 = 465)

    # Kimberly: 4:30 PM to 9:00 PM
    kimberly_available_start = 450  # 4:30 PM is 7.5 hours after 9:00 AM (7*60 + 30 = 450)
    kimberly_available_end = 720     # 9:00 PM is 12 hours after 9:00 AM (12*60 = 720)

    # Patricia: 6:00 PM to 9:15 PM
    patricia_available_start = 540   # 6:00 PM is 9 hours after 9:00 AM (9*60 = 540)
    patricia_available_end = 735     # 9:15 PM is 12 hours and 15 minutes after 9:00 AM (12*60 + 15 = 735)

    # Minimum meeting times
    helen_min_time = 120
    kimberly_min_time = 45
    patricia_min_time = 120

    # Constraints for Helen
    s.add(helen_start >= helen_available_start)
    s.add(helen_end <= helen_available_end)
    s.add(helen_end - helen_start >= helen_min_time)
    s.add(helen_start >= 0)  # Can't start before 9:00 AM (arrival time)

    # Constraints for Kimberly
    s.add(kimberly_start >= kimberly_available_start)
    s.add(kimberly_end <= kimberly_available_end)
    s.add(kimberly_end - kimberly_start >= kimberly_min_time)

    # Constraints for Patricia
    s.add(patricia_start >= patricia_available_start)
    s.add(patricia_end <= patricia_available_end)
    s.add(patricia_end - patricia_start >= patricia_min_time)

    # Travel constraints
    # From Nob Hill to North Beach: 8 minutes
    # So, Helen's meeting starts at least 8 minutes after 9:00 AM
    s.add(helen_start >= 8)

    # From North Beach to Fisherman's Wharf: 5 minutes
    # So, Kimberly's meeting starts >= helen_end + 5
    s.add(kimberly_start >= helen_end + 5)

    # From Fisherman's Wharf to Bayview: 26 minutes
    # So, Patricia's meeting starts >= kimberly_end + 26
    s.add(patricia_start >= kimberly_end + 26)

    # Check if the constraints are satisfiable
    if s.check() == sat:
        m = s.model()
        # Convert minutes back to time format
        def minutes_to_time(minutes):
            total_hours = 9 + (minutes // 60)
            total_minutes = minutes % 60
            am_pm = "AM" if total_hours < 12 else "PM"
            if total_hours > 12:
                total_hours -= 12
            return f"{total_hours}:{total_minutes:02d} {am_pm}"

        helen_s = m.evaluate(helen_start).as_long()
        helen_e = m.evaluate(helen_end).as_long()
        kimberly_s = m.evaluate(kimberly_start).as_long()
        kimberly_e = m.evaluate(kimberly_end).as_long()
        patricia_s = m.evaluate(patricia_start).as_long()
        patricia_e = m.evaluate(patricia_end).as_long()

        print("SOLUTION:")
        print(f"Meet Helen at North Beach from {minutes_to_time(helen_s)} to {minutes_to_time(helen_e)}")
        print(f"Meet Kimberly at Fisherman's Wharf from {minutes_to_time(kimberly_s)} to {minutes_to_time(kimberly_e)}")
        print(f"Meet Patricia at Bayview from {minutes_to_time(patricia_s)} to {minutes_to_time(patricia_e)}")
    else:
        print("No valid schedule found.")

solve_scheduling()